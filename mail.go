// Copyright 2015 Konstantin Kulikov. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Package mail implements mail parser and generator.
//
// This package doesn't expose any email internals,
// but is suitable and easy to use in scenarios like
// parse message, convert html bits to text, determine
// customer by email address, create ticket in a ticket
// system and reply back with TT ID.
//
// 	msg, err := mail.ReadMessage(r.Body)
// 	if err != nil {
// 		return err
// 	}
//
// 	customer, err := FindCustomer(msg.From)
// 	if err != nil {
// 		return err
// 	}
//
// 	tt, err := customer.CreateTT(msg.Subject, msg.Text)
// 	if err != nil {
// 		return err
// 	}
//
// 	nmsg := msg.Reply(emailHelpdesk, fmt.Sprintf(ReplyFmt, tt.ID), nil)
// 	nmsg.Subject = fmt.Sprintf("Re: [TT:%v] %v", tt.ID, msg.Subject)
// 	if err := nmsg.Send(); err != nil {
// 		return err
// 	}
//
package mail

import (
	"bytes"
	"encoding/base64"
	"fmt"
	"io"
	"io/ioutil"
	"math/rand"
	"mime"
	"mime/multipart"
	"mime/quotedprintable"
	"net/mail"
	"net/smtp"
	"net/textproto"
	"os"
	"strings"
	"time"
	"unicode/utf8"

	"golang.org/x/net/html/charset"
	"golang.org/x/text/transform"

	"github.com/jaytaylor/html2text"
)

// Message represents Email message.
type Message struct {
	ID         string
	ReturnPath string
	From       string
	To         []string
	CC         []string
	Subject    string
	Date       time.Time
	HTML       string
	Body       string
	Parts      []Part
	Headers    map[string]string
}

// Part represents attachment in message.
type Part struct {
	Name string
	Data []byte
}

// NewMessage creates new message.
func NewMessage(from string, to []string, cc []string, subject, body string, headers map[string]string) *Message {
	return &Message{
		ID:         makeID(),
		ReturnPath: from,
		From:       from,
		To:         to,
		CC:         cc,
		Subject:    subject,
		Date:       time.Now(),
		Body:       body,
		Headers:    headers,
	}
}

// ReadMessage reads message from r.
// Using Send() on read messages can result in garbage in headers,
// make sure to remove unnecessary ones, before sending.
func ReadMessage(r io.Reader) (*Message, error) {
	// TODO: do not read whole body at once.
	rawheaders, body, err := readMessage(r)
	if err != nil {
		return nil, err
	}

	m := new(Message)

	// MessageID
	if id := rawheaders.Get("Message-Id"); id != "" {
		m.ID = id
	} else {
		m.ID = makeID()
	}

	// Date
	if date, err := rawheaders.Date(); err == nil {
		m.Date = date
	} else {
		m.Date = time.Now()
	}

	// Subject
	if subject, err := decodeHeader(rawheaders.Get("Subject")); err == nil && subject != "" {
		m.Subject = subject
	} else if err != nil {
		return nil, fmt.Errorf("decode header: %v", err)
	} else {
		m.Subject = "No subject"
	}

	// Return-Path
	if h := rawheaders.Get("Return-Path"); h != "" {
		retpath, err := decodeAddress(h)
		if err != nil {
			return nil, fmt.Errorf("parse return-path: %v", err)
		}
		if len(retpath) > 0 {
			m.ReturnPath = retpath[0]
		}
	}

	// From
	if h := rawheaders.Get("From"); h != "" {
		from, err := decodeAddress(h)
		if err != nil {
			return nil, fmt.Errorf("parse from: %v", err)
		}
		if len(from) > 0 {
			m.From = from[0]
		}
	}

	// To
	if h := rawheaders.Get("To"); h != "" {
		to, err := decodeAddress(h)
		if err != nil {
			return nil, fmt.Errorf("parse to: %v", err)
		}
		m.To = to
	} else {
		m.To = make([]string, 0)
	}

	// CC
	if h := rawheaders.Get("Cc"); h != "" {
		cc, err := decodeAddress(h)
		if err != nil {
			return nil, fmt.Errorf("parse cc: %v", err)
		}
		m.CC = cc
	} else {
		m.CC = make([]string, 0)
	}

	// Reject messages without "from" header.
	if m.From == "" {
		return nil, fmt.Errorf("header From not found in message")
	}

	// If return-path is unset, set it using from.
	if m.ReturnPath == "" {
		m.ReturnPath = m.From
	}

	// TODO: use text.Transform to replace invalid symbols
	// with spaces for both base64 and quoted-printable.
	if m.From == "helpdesk@ttk.ru" {
		for i := range body {
			if body[i] == 0xbb {
				body[i] = ' '
			}
		}
	}

	// Add missing \n to body. Go's quoted-printable decoder requires this.
	if body[len(body)-1] != '\n' {
		body = append(body, '\n')
	}

	// Decode rest of the headers.
	headers := make(map[string]string)
	for k, v := range rawheaders {
		switch k {
		case "Message-Id", "Subject", "Date", "Return-Path", "From", "To", "Cc":
			continue
		}
		for _, w := range v {
			decoded, err := decodeHeader(w)
			if err != nil {
				return nil, fmt.Errorf("decode header: %v", err)
			}
			str := headers[k]
			if str != "" {
				str += " "
			}
			headers[k] = str + decoded
		}
	}
	m.Headers = headers

	// Decode body.
	if err := m.decodeBody(bytes.NewReader(body), textproto.MIMEHeader(rawheaders)); err != nil {
		return nil, fmt.Errorf("decode body: %v", err)
	}

	// If body is HTML, convert it to text.
	if len(m.Body) == 0 && len(m.HTML) > 0 {
		m.Body, err = html2text.FromString(m.HTML)
		if err != nil {
			return nil, err
		}
	}

	return m, nil
}

// Reply generates reply to m.
func (m *Message) Reply(from, body string, cc []string) *Message {
	subj := m.Subject
	if !strings.HasPrefix(strings.ToLower(subj), "re:") {
		subj = fmt.Sprintf("Re: %v", m.Subject)
	}
	headers := map[string]string{
		"In-Reply-To": m.ID,
		"References":  m.ID,
	}

	nbody := new(bytes.Buffer)
	nbody.WriteString(body)
	nbody.WriteString("\n\n")
	nbody.WriteString("-------- Original message --------\n")
	lines := strings.Split(m.Body, "\n")
	for _, line := range lines {
		nbody.WriteString(">")
		nbody.WriteString(line)
		nbody.WriteString("\n")
	}

	return NewMessage(from, []string{m.ReturnPath}, cc, subj, nbody.String(), headers)
}

// ReplyAll generates reply all to m.
func (m *Message) ReplyAll(from, body string) *Message {
	var (
		cc   []string
		seen = make(map[string]bool)
	)

	if m.ReturnPath != m.From {
		cc = append(cc, m.From)
		seen[m.From] = true
	}

	for _, v := range m.To {
		if _, exists := seen[v]; !exists {
			cc = append(cc, v)
			seen[v] = true
		}
	}

	for _, v := range m.CC {
		if _, exists := seen[v]; !exists {
			cc = append(cc, v)
			seen[v] = true
		}
	}

	return m.Reply(from, body, cc)
}

// Forward generates forward message for m.
func (m *Message) Forward(from string, to []string, cc []string, body string) *Message {
	subj := m.Subject
	if !strings.HasPrefix(strings.ToLower(subj), "fwd:") {
		subj = fmt.Sprintf("Fwd: %v", m.Subject)
	}
	headers := map[string]string{
		"In-Reply-To": m.ID,
		"References":  m.ID,
	}

	nbody := new(bytes.Buffer)
	nbody.WriteString(body)
	nbody.WriteString("\n\n")
	nbody.WriteString("-------- Forwarded message --------\n")
	nbody.WriteString(m.Body)

	return NewMessage(from, to, cc, subj, nbody.String(), headers)
}

// Send sends message via 127.0.0.1:25.
func (m *Message) Send() error {
	b, err := m.Marshall()
	if err != nil {
		return fmt.Errorf("marshall body: %v", err)
	}
	var recv []string
	recv = append(recv, m.To...)
	recv = append(recv, m.CC...)
	return smtp.SendMail("127.0.0.1:25", nil, m.From, recv, b)
}

// Marshall builds a textual representation of a message with headers and quoted-printable body.
// It ignores ReturnPath, HTML and Parts.
func (m *Message) Marshall() ([]byte, error) {
	q := mime.QEncoding
	buf := new(bytes.Buffer)
	buf.WriteString(fmt.Sprintf("From: <%v>\n", m.From))
	if len(m.To) > 0 {
		buf.WriteString("To: ")
		for i, v := range m.To {
			if i != 0 {
				buf.WriteString(", ")
			}
			buf.WriteString(fmt.Sprintf("<%v>", v))
		}
		buf.WriteString("\n")
	}
	if len(m.CC) > 0 {
		buf.WriteString("CC: ")
		for i, v := range m.CC {
			if i != 0 {
				buf.WriteString(", ")
			}
			buf.WriteString(fmt.Sprintf("<%v>", v))
		}
		buf.WriteString("\n")
	}
	buf.WriteString(fmt.Sprintf("Message-ID: %v\n", m.ID))
	buf.WriteString(fmt.Sprintf("Subject: %v\n", q.Encode("utf-8", m.Subject)))
	buf.WriteString(fmt.Sprintf("Date: %v\n", m.Date.Format("Mon, 2 Jan 2006 15:04:05 -0700 (MST)")))
	for k, v := range m.Headers {
		switch k {
		case "Content-Type", "Content-Transfer-Encoding", "Content-Disposition":
			continue
		}
		buf.WriteString(fmt.Sprintf("%v: %v\n", k, q.Encode("utf-8", v)))
	}
	buf.WriteString("Content-Type: text/plain; charset=utf-8;\n")
	buf.WriteString("Content-Transfer-Encoding: quoted-printable\n")
	buf.WriteString("\n")

	w := quotedprintable.NewWriter(buf)
	if _, err := w.Write([]byte(m.Body)); err != nil {
		return nil, err
	}
	if err := w.Close(); err != nil {
		return nil, err
	}

	return buf.Bytes(), nil
}

// Receivers return joined list from To and CC separated with comma.
func (m *Message) Receivers() string {
	var recv []string
	recv = append(recv, m.To...)
	recv = append(recv, m.CC...)
	return strings.Join(recv, ", ")
}

// decodeBody parses body of a message, filling m.Body, m.HTML and m.Parts.
func (m *Message) decodeBody(r io.Reader, h textproto.MIMEHeader) error {
	cth := h.Get("Content-Type")
	if cth == "" {
		cth = "text/plain"
	}
	ct, ctp, err := mime.ParseMediaType(cth)
	if err != nil {
		return fmt.Errorf("invalid content-type: %q", cth)
	}

	// Find name.
	filename := ctp["name"]
	if filename == "" {
		cdh := h.Get("Content-Disposition")
		if cdh != "" {
			_, cdp, err := mime.ParseMediaType(cdh)
			if err != nil {
				return fmt.Errorf("invalid content-disposition: %q", cdh)
			}
			filename = cdp["filename"]

		}
	}

	// If it has filename, add as attachment.
	if filename != "" {
		name, err := decodeHeader(filename)
		if err != nil {
			return fmt.Errorf("decode filename: %v", err)
		}
		data, err := ioutil.ReadAll(decodeTransfer(r, h.Get("Content-Transfer-Encoding")))
		if err != nil {
			return fmt.Errorf("read attachment: %v", err)
		}

		m.Parts = append(m.Parts, Part{Name: name, Data: data})
		return nil
	}

	if ct == "text/plain" || ct == "text/html" {
		data, err := ioutil.ReadAll(decodeTransfer(r, h.Get("Content-Transfer-Encoding")))
		if err != nil {
			return fmt.Errorf("read body: %v", err)
		}

		body, err := decodeCharset(string(data), ctp["charset"])
		if err != nil {
			return fmt.Errorf("charsetDecode: %v", err)
		}

		if ct == "text/html" {
			m.HTML += body
			return nil
		}

		m.Body += body
		return nil
	}

	if strings.HasPrefix(ct, "multipart/") {
		r := multipart.NewReader(r, ctp["boundary"])
		for {
			p, err := r.NextPart()
			if err != nil {
				if err == io.EOF {
					break
				}
				return fmt.Errorf("next part: %q", err)
			}

			if err := m.decodeBody(p, p.Header); err != nil {
				p.Close() // p.Close is also called automatically by r.NextPart.
				return err
			}
		}
		return nil
	}

	// TODO: decide what to do with this.
	//return fmt.Errorf("content-type without filename: %q", ct)
	return nil
}

// readMessage reads message from r and parses headers.
func readMessage(r io.Reader) (headers mail.Header, body []byte, err error) {
	m, err := mail.ReadMessage(r)
	if err != nil {
		return nil, nil, err
	}

	bodyBytes, err := ioutil.ReadAll(m.Body)
	if err != nil {
		return nil, nil, err
	}

	return m.Header, bodyBytes, nil
}

// decodeAddress parses address line.
func decodeAddress(rawheader string) ([]string, error) {
	if rawheader == "" {
		return nil, nil
	}

	header, err := decodeHeader(rawheader)
	if err != nil {
		return nil, err
	}

	var (
		addrs []string
		buf   bytes.Buffer
		state = "outside"
	)
	for _, v := range header {
		switch state {
		case "outside":
			if v == '>' {
				continue
			}
			if v == '<' {
				state = "inside"
				continue
			}
		case "inside":
			if v == '<' {
				buf.Reset()
				continue
			}
			if v == '>' {
				addrs = append(addrs, buf.String())
				buf.Reset()
				state = "outside"
				continue
			}
			buf.WriteRune(v)
		}
	}

	// If no addresses in angular brackets found, split by comma.
	if len(addrs) == 0 {
		header = strings.Replace(header, " ", "", -1)
		return strings.Split(header, ","), nil
	}

	return addrs, nil
}

// decodeHeader decodes header, detecting its charset.
// It guarantees to produce utf-8 string or error.
func decodeHeader(rawheader string) (string, error) {
	dec := &mime.WordDecoder{
		CharsetReader: charset.NewReaderLabel,
	}

	header, err := dec.DecodeHeader(rawheader)
	if err != nil {
		return header, err
	}

	if !utf8.ValidString(header) {
		nheader, err := decodeCharset(header, "")
		if err != nil {
			return header, err
		}

		if !utf8.ValidString(nheader) {
			return header, fmt.Errorf("decode header: non-utf8 byte left after decode")
		}

		return nheader, nil
	}

	return header, nil
}

// FailReader returns error on first read.
type failReader struct {
	err error
}

// Read returns error on read.
func (r failReader) Read(b []byte) (n int, err error) {
	return 0, r.err
}

// DecodeTransfer decodes base64, quoted-printable or plain text.
func decodeTransfer(r io.Reader, label string) io.Reader {
	switch label {
	case "base64", "Base64", "BASE64":
		return base64.NewDecoder(base64.StdEncoding, r)
	case "quoted-printable", "Quoted-Printable", "QUOTED-PRINTABLE":
		return quotedprintable.NewReader(r)
	case "", "7bit", "7Bit", "7BIT", "8bit", "8Bit", "8BIT", "binary", "Binary", "BINARY":
		return r
	default:
		return failReader{fmt.Errorf("unsupported transfer encoding: %v", label)}
	}
}

// DecodeCharset detects charset of str decodes it.
func decodeCharset(str, label string) (nstr string, err error) {
	enc, _ := charset.Lookup(label)
	if enc == nil {
		enc, _, _ = charset.DetermineEncoding([]byte(str), "text/plain")
	}

	nstr, _, err = transform.String(enc.NewDecoder(), str)
	if err != nil {
		return nstr, err
	}

	// If resulted string is not valid utf8, decode again using iso-8859-15.
	// If that doesn't work, return error.
	if !utf8.ValidString(nstr) {
		if label == "iso-8859-15" {
			return nstr, fmt.Errorf("couldn't correctly decode string using charset %q", label)
		}
		return decodeCharset(str, "iso-8859-15")
	}

	return nstr, nil
}

// MakeID generated random Message-ID.
func makeID() string {
	now := time.Now().UTC().Format("20060102150405")
	pid := os.Getpid()
	val := rand.Intn(100000)
	host, _ := os.Hostname()
	if host == "" {
		host = "localhost"
	}

	return fmt.Sprintf("<%v.%v.%v@%v>", now, pid, val, host)
}
