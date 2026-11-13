/*
 * DateFix core: rewrites the capture date stored inside photo and video files
 * without touching the encoded image or video data.
 *
 *   JPEG  - EXIF (APP1) + XMP
 *   PNG   - eXIf chunk + XMP (iTXt)
 *   HEIC  - Exif item + XMP item (ISOBMFF meta/iloc)
 *   MOV / MP4 / M4V - mvhd/tkhd/mdhd times + com.apple.quicktime.creationdate + ©day
 *
 * A target time is {y, mo, d, h, mi, s, offMin}, offMin = minutes east of UTC.
 */
(function (global) {
  'use strict';

  class DFError extends Error {}

  // ---------- bytes ----------
  const u16BE = (u8, o) => (u8[o] << 8) | u8[o + 1];
  const u32BE = (u8, o) => u8[o] * 0x1000000 + ((u8[o + 1] << 16) | (u8[o + 2] << 8) | u8[o + 3]);
  const u64BE = (u8, o) => u32BE(u8, o) * 0x100000000 + u32BE(u8, o + 4);
  const str = (u8, o, n) => { let s = ''; for (let i = 0; i < n && o + i < u8.length; i++) s += String.fromCharCode(u8[o + i]); return s; };
  const str4 = (u8, o) => str(u8, o, 4);
  const latin1 = s => Uint8Array.from(s, c => c.charCodeAt(0) & 0xff);
  const utf8 = s => new TextEncoder().encode(s);
  const ascii = s => { const b = new Uint8Array(s.length + 1); b.set(latin1(s)); return b; };

  function readN(u8, o, n) {
    if (n === 0) return 0;
    if (n === 2) return u16BE(u8, o);
    if (n === 4) return u32BE(u8, o);
    if (n === 8) return u64BE(u8, o);
    throw new DFError('지원하지 않는 파일 구조예요.');
  }
  function bytesN(n, v) {
    const b = new Uint8Array(n);
    for (let i = n - 1; i >= 0; i--) { b[i] = v % 256; v = Math.floor(v / 256); }
    if (v > 0) throw new DFError('파일이 너무 커서 처리할 수 없어요.');
    return b;
  }
  function concat(parts) {
    let n = 0; for (const p of parts) n += p.length;
    const out = new Uint8Array(n); let o = 0;
    for (const p of parts) { out.set(p, o); o += p.length; }
    return out;
  }
  const startsWith = (u8, o, sig) => sig.every((c, i) => u8[o + i] === c);

  // ---------- dates ----------
  const pad = (n, w = 2) => String(n).padStart(w, '0');
  const offsetStr = (m, colon = true) => (m >= 0 ? '+' : '-') + pad(Math.floor(Math.abs(m) / 60)) + (colon ? ':' : '') + pad(Math.abs(m) % 60);
  const exifDate = t => `${t.y}:${pad(t.mo)}:${pad(t.d)} ${pad(t.h)}:${pad(t.mi)}:${pad(t.s)}`;
  const isoDate = (t, colon = true) => `${t.y}-${pad(t.mo)}-${pad(t.d)}T${pad(t.h)}:${pad(t.mi)}:${pad(t.s)}${offsetStr(t.offMin, colon)}`;
  const utcMillis = t => Date.UTC(t.y, t.mo - 1, t.d, t.h, t.mi, t.s) - t.offMin * 60000;
  const QT_EPOCH = 2082844800; // seconds 1904-01-01 -> 1970-01-01

  function parseExifDate(s, off) {
    const m = /^(\d{4}):(\d{2}):(\d{2}) (\d{2}):(\d{2}):(\d{2})/.exec(s || '');
    if (!m || m[1] === '0000') return null;
    const t = { y: +m[1], mo: +m[2], d: +m[3], h: +m[4], mi: +m[5], s: +m[6], offMin: null };
    const o = /^([+-])(\d{2}):?(\d{2})/.exec(off || '');
    if (o) t.offMin = (o[1] === '-' ? -1 : 1) * (+o[2] * 60 + +o[3]);
    return t;
  }
  function parseIsoDate(s) {
    const m = /^(\d{4})-(\d{2})-(\d{2})T(\d{2}):(\d{2}):(\d{2})(?:\.\d+)?(Z|[+-]\d{2}:?\d{2})?/.exec(s || '');
    if (!m) return null;
    const t = { y: +m[1], mo: +m[2], d: +m[3], h: +m[4], mi: +m[5], s: +m[6], offMin: null };
    if (m[7] === 'Z') t.offMin = 0;
    else if (m[7]) t.offMin = (m[7][0] === '-' ? -1 : 1) * (+m[7].slice(1, 3) * 60 + +m[7].slice(-2));
    return t;
  }
  function fromUtcSeconds(secs) {
    if (!secs) return null;
    const d = new Date(secs * 1000);
    return { y: d.getFullYear(), mo: d.getMonth() + 1, d: d.getDate(), h: d.getHours(), mi: d.getMinutes(), s: d.getSeconds(), offMin: -d.getTimezoneOffset() };
  }

  // ---------- TIFF / EXIF ----------
  const TYPE_SIZE = [0, 1, 1, 2, 4, 8, 1, 1, 2, 4, 8, 4, 8, 4];
  const EXIF_PTR = 0x8769, GPS_PTR = 0x8825, INTEROP_PTR = 0xA005;
  const DATE_TAGS = { ifd0: [0x0132], exif: [0x9003, 0x9004] };
  const OFFSET_TAGS = [0x9010, 0x9011, 0x9012];

  function parseTiff(u8) {
    if (u8.length < 8) throw new DFError('EXIF 정보가 손상되었어요.');
    const bo = str(u8, 0, 2);
    if (bo !== 'II' && bo !== 'MM') throw new DFError('EXIF 정보가 손상되었어요.');
    const le = bo === 'II';
    const dv = new DataView(u8.buffer, u8.byteOffset, u8.byteLength);
    const u16 = o => dv.getUint16(o, le), u32 = o => dv.getUint32(o, le);
    if (u16(2) !== 42) throw new DFError('EXIF 정보가 손상되었어요.');
    const seen = new Set();

    function readIFD(off, subTags) {
      if (!off || off + 2 > u8.length || seen.has(off)) return null;
      seen.add(off);
      const n = u16(off);
      if (off + 2 + n * 12 > u8.length) return null;
      const ifd = { entries: [], subs: {}, next: 0, thumb: null };
      for (let i = 0; i < n; i++) {
        const e = off + 2 + i * 12;
        const tag = u16(e), type = u16(e + 2), count = u32(e + 4);
        const ts = TYPE_SIZE[type] || 0;
        if (!ts) continue;
        const size = ts * count;
        if (subTags.includes(tag) && size === 4) {
          const sub = readIFD(u32(e + 8), tag === EXIF_PTR ? [INTEROP_PTR] : []);
          if (sub) ifd.subs[tag] = sub;
          continue;
        }
        const pos = size <= 4 ? e + 8 : u32(e + 8);
        if (pos + size > u8.length) continue;
        ifd.entries.push({ tag, type, count, pos, data: u8.slice(pos, pos + size) });
      }
      const np = off + 2 + n * 12;
      ifd.next = np + 4 <= u8.length ? u32(np) : 0;
      return ifd;
    }

    const ifd0 = readIFD(u32(4), [EXIF_PTR, GPS_PTR]);
    if (!ifd0) throw new DFError('EXIF 정보가 손상되었어요.');
    let ifd1 = ifd0.next ? readIFD(ifd0.next, []) : null;
    if (ifd1) {
      const val = tag => {
        const e = ifd1.entries.find(x => x.tag === tag);
        if (!e) return null;
        const d = new DataView(e.data.buffer);
        return e.type === 3 ? d.getUint16(0, le) : e.type === 4 ? d.getUint32(0, le) : null;
      };
      const off = val(0x0201), len = val(0x0202);
      if (off != null && len && off + len <= u8.length) ifd1.thumb = u8.slice(off, off + len);
      ifd1.entries = ifd1.entries.filter(e => e.tag !== 0x0201 && (ifd1.thumb || e.tag !== 0x0202));
    }
    return { le, ifd0, ifd1 };
  }

  function serializeTiff(t) {
    const { le } = t;
    const evenLen = n => n + (n & 1);
    const listOf = ifd => {
      const l = ifd.entries.map(e => ({ tag: e.tag, type: e.type, count: e.count, data: e.data }));
      for (const k in ifd.subs) l.push({ tag: +k, type: 4, count: 1, sub: ifd.subs[k] });
      if (ifd.thumb) l.push({ tag: 0x0201, type: 4, count: 1, thumb: ifd.thumb });
      return l.sort((a, b) => a.tag - b.tag);
    };
    const size = ifd => {
      let s = 2 + 12 * listOf(ifd).length + 4;
      for (const e of ifd.entries) if (e.data.length > 4) s += evenLen(e.data.length);
      for (const k in ifd.subs) s += size(ifd.subs[k]);
      if (ifd.thumb) s += evenLen(ifd.thumb.length);
      return s;
    };
    const out = new Uint8Array(8 + size(t.ifd0) + (t.ifd1 ? size(t.ifd1) : 0));
    const dv = new DataView(out.buffer);
    out.set(latin1(le ? 'II' : 'MM'));
    dv.setUint16(2, 42, le);
    dv.setUint32(4, 8, le);

    function write(ifd, off) {
      const list = listOf(ifd);
      dv.setUint16(off, list.length, le);
      let data = off + 2 + 12 * list.length + 4;
      const later = [];
      list.forEach((e, i) => {
        const p = off + 2 + 12 * i;
        dv.setUint16(p, e.tag, le); dv.setUint16(p + 2, e.type, le); dv.setUint32(p + 4, e.count, le);
        if (e.sub || e.thumb) later.push([e, p + 8]);
        else if (e.data.length <= 4) out.set(e.data, p + 8);
        else { dv.setUint32(p + 8, data, le); out.set(e.data, data); data += evenLen(e.data.length); }
      });
      const nextPos = off + 2 + 12 * list.length;
      for (const [e, p] of later) {
        dv.setUint32(p, data, le);
        if (e.sub) data = write(e.sub, data).end;
        else { out.set(e.thumb, data); data += evenLen(e.thumb.length); }
      }
      return { end: data, nextPos };
    }
    const r0 = write(t.ifd0, 8);
    if (t.ifd1) { dv.setUint32(r0.nextPos, r0.end, le); write(t.ifd1, r0.end); }
    return out;
  }

  function setEntry(ifd, tag, type, data) {
    const e = { tag, type, count: data.length, data };
    const i = ifd.entries.findIndex(x => x.tag === tag);
    if (i >= 0) ifd.entries[i] = e; else ifd.entries.push(e);
  }

  function tiffDate(t) {
    const ex = t.ifd0.subs[EXIF_PTR];
    const get = (ifd, tag) => { const e = ifd && ifd.entries.find(x => x.tag === tag); return e ? str(e.data, 0, e.data.length).replace(/\0.*$/, '') : null; };
    return parseExifDate(get(ex, 0x9003), get(ex, 0x9011)) || parseExifDate(get(ex, 0x9004), get(ex, 0x9012)) || parseExifDate(get(t.ifd0, 0x0132), get(ex, 0x9010));
  }

  // Overwrites existing date strings at their current positions. Returns
  // patches relative to the TIFF header, or null when a rebuild is needed.
  function tiffInPlace(t, tm) {
    const ex = t.ifd0.subs[EXIF_PTR];
    if (!ex || !ex.entries.some(e => e.tag === 0x9003)) return null;
    const patches = [];
    const put = (e, s, min) => {
      if (e.type !== 2 || e.count < min) return false;
      const b = new Uint8Array(e.count); b.set(latin1(s));
      patches.push({ pos: e.pos, bytes: b });
      return true;
    };
    for (const [ifd, tags] of [[t.ifd0, DATE_TAGS.ifd0], [ex, DATE_TAGS.exif]])
      for (const e of ifd.entries) if (tags.includes(e.tag) && !put(e, exifDate(tm), 20)) return null;
    for (const e of ex.entries) if (OFFSET_TAGS.includes(e.tag) && !put(e, offsetStr(tm.offMin), 7)) return null;
    return patches;
  }

  function tiffRebuild(t, tm) {
    t = t || { le: false, ifd0: { entries: [], subs: {} }, ifd1: null };
    const dt = ascii(exifDate(tm)), off = ascii(offsetStr(tm.offMin));
    setEntry(t.ifd0, 0x0132, 2, dt);
    let ex = t.ifd0.subs[EXIF_PTR];
    if (!ex) {
      ex = { entries: [{ tag: 0x9000, type: 7, count: 4, data: latin1('0232') }], subs: {} };
      t.ifd0.subs[EXIF_PTR] = ex;
    }
    setEntry(ex, 0x9003, 2, dt);
    setEntry(ex, 0x9004, 2, dt);
    for (const tag of OFFSET_TAGS) setEntry(ex, tag, 2, off);
    return t;
  }

  // Returns {patches} (relative to TIFF start) or {bytes} (a whole new TIFF block).
  function editTiff(tiffBytes, tm, maxLen = Infinity) {
    let t = null;
    if (tiffBytes) { try { t = parseTiff(tiffBytes); } catch (e) { t = null; } }
    if (t) { const p = tiffInPlace(t, tm); if (p) return { patches: p }; }
    t = tiffRebuild(t, tm);
    let bytes = serializeTiff(t);
    if (bytes.length > maxLen && t.ifd1) { t.ifd1 = null; bytes = serializeTiff(t); }
    if (bytes.length > maxLen) throw new DFError('EXIF 정보가 너무 커서 처리할 수 없어요.');
    return { bytes };
  }

  // ---------- XMP ----------
  const XMP_TAGS = 'xmp:CreateDate|xmp:ModifyDate|xmp:MetadataDate|photoshop:DateCreated|exif:DateTimeOriginal|exif:DateTimeDigitized|tiff:DateTime';
  function editXmp(text, tm) {
    const iso = isoDate(tm);
    return text
      .replace(new RegExp(`((?:${XMP_TAGS})\\s*=\\s*")[^"]*(")`, 'g'), `$1${iso}$2`)
      .replace(new RegExp(`(<(${XMP_TAGS})>)[^<]*(</\\2>)`, 'g'), `$1${iso}$3`);
  }
  function xmpDate(text) {
    const m = new RegExp(`(?:photoshop:DateCreated|exif:DateTimeOriginal|xmp:CreateDate)(?:\\s*=\\s*"|>)([^"<]*)`).exec(text);
    return m ? parseIsoDate(m[1]) : null;
  }

  // ---------- output ----------
  // patches: [{start, end, bytes}] absolute in the source file; untouched ranges stay as Blob slices.
  function assemble(file, patches, type) {
    patches = patches.slice().sort((a, b) => a.start - b.start);
    const parts = []; let cur = 0;
    for (const p of patches) {
      if (p.start < cur) throw new DFError('파일 구조가 예상과 달라요.');
      parts.push(file.slice(cur, p.start), p.bytes);
      cur = p.end;
    }
    parts.push(file.slice(cur));
    return new Blob(parts, { type });
  }

  // ---------- JPEG ----------
  const EXIF_HDR = [0x45, 0x78, 0x69, 0x66, 0, 0];
  const XMP_HDR = Array.from(latin1('http://ns.adobe.com/xap/1.0/\0'));

  function jpegSegments(u8) {
    const segs = []; let p = 2;
    while (p + 4 <= u8.length && u8[p] === 0xFF) {
      const m = u8[p + 1];
      if (m === 0xFF) { p++; continue; }
      if (m === 0x01 || (m >= 0xD0 && m <= 0xD8)) { p += 2; continue; }
      if (m === 0xD9 || m === 0xDA) break;
      const len = u16BE(u8, p + 2);
      segs.push({ marker: m, start: p, end: p + 2 + len });
      p += 2 + len;
    }
    return segs;
  }
  const jpegExif = (u8, segs) => segs.find(s => s.marker === 0xE1 && startsWith(u8, s.start + 4, EXIF_HDR));
  const jpegXmp = (u8, segs) => segs.find(s => s.marker === 0xE1 && startsWith(u8, s.start + 4, XMP_HDR));

  function jpegRead(u8) {
    const segs = jpegSegments(u8);
    const ex = jpegExif(u8, segs);
    if (ex) { try { const d = tiffDate(parseTiff(u8.subarray(ex.start + 10, ex.end))); if (d) return d; } catch (e) { /* fall through */ } }
    const xs = jpegXmp(u8, segs);
    return xs ? xmpDate(new TextDecoder().decode(u8.subarray(xs.start + 4 + XMP_HDR.length, xs.end))) : null;
  }

  function jpegEdit(file, u8, tm) {
    const segs = jpegSegments(u8);
    const patches = [];
    const ex = jpegExif(u8, segs);
    const tiffStart = ex ? ex.start + 10 : 0;
    const r = editTiff(ex ? u8.subarray(tiffStart, ex.end) : null, tm, 65535 - 2 - 6);
    if (r.patches) {
      for (const p of r.patches) patches.push({ start: tiffStart + p.pos, end: tiffStart + p.pos + p.bytes.length, bytes: p.bytes });
    } else {
      const seg = concat([Uint8Array.of(0xFF, 0xE1), bytesN(2, 2 + 6 + r.bytes.length), Uint8Array.from(EXIF_HDR), r.bytes]);
      if (ex) patches.push({ start: ex.start, end: ex.end, bytes: seg });
      else {
        const at = segs[0] && segs[0].marker === 0xE0 ? segs[0].end : 2;
        patches.push({ start: at, end: at, bytes: seg });
      }
    }
    const xs = jpegXmp(u8, segs);
    if (xs) {
      const body = xs.start + 4 + XMP_HDR.length;
      const text = new TextDecoder().decode(u8.subarray(body, xs.end));
      const next = editXmp(text, tm);
      if (next !== text) {
        const nb = utf8(next);
        if (2 + XMP_HDR.length + nb.length <= 65535) {
          patches.push({ start: xs.start, end: xs.end, bytes: concat([Uint8Array.of(0xFF, 0xE1), bytesN(2, 2 + XMP_HDR.length + nb.length), Uint8Array.from(XMP_HDR), nb]) });
        }
      }
    }
    return assemble(file, patches, 'image/jpeg');
  }

  // ---------- PNG ----------
  const CRC_TABLE = (() => {
    const t = new Uint32Array(256);
    for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320 ^ (c >>> 1) : c >>> 1; t[n] = c >>> 0; }
    return t;
  })();
  function crc32(u8) { let c = 0xFFFFFFFF; for (let i = 0; i < u8.length; i++) c = CRC_TABLE[(c ^ u8[i]) & 0xff] ^ (c >>> 8); return (c ^ 0xFFFFFFFF) >>> 0; }
  function pngChunk(type, data) {
    const td = concat([latin1(type), data]);
    return concat([bytesN(4, data.length), td, bytesN(4, crc32(td))]);
  }
  function pngChunks(u8) {
    const out = []; let p = 8;
    while (p + 12 <= u8.length) {
      const len = u32BE(u8, p), type = str4(u8, p + 4);
      out.push({ type, start: p, data: p + 8, dataEnd: p + 8 + len, end: p + 12 + len });
      p += 12 + len;
      if (type === 'IEND') break;
    }
    return out;
  }
  async function inflate(u8) {
    const ds = new DecompressionStream('deflate');
    return new Uint8Array(await new Response(new Blob([u8]).stream().pipeThrough(ds)).arrayBuffer());
  }
  async function pngXmp(u8, c) {
    if (c.type !== 'iTXt') return null;
    const d = u8.subarray(c.data, c.dataEnd);
    const kwEnd = d.indexOf(0);
    if (str(d, 0, kwEnd) !== 'XML:com.adobe.xmp') return null;
    const compressed = d[kwEnd + 1] === 1;
    let p = kwEnd + 3;
    p = d.indexOf(0, p) + 1; // language tag
    p = d.indexOf(0, p) + 1; // translated keyword
    const head = d.slice(0, p); head[kwEnd + 1] = 0; head[kwEnd + 2] = 0;
    const body = compressed ? await inflate(d.subarray(p)) : d.subarray(p);
    return { head, text: new TextDecoder().decode(body) };
  }

  async function pngRead(u8) {
    for (const c of pngChunks(u8)) {
      if (c.type === 'eXIf') { try { const d = tiffDate(parseTiff(u8.subarray(c.data, c.dataEnd))); if (d) return d; } catch (e) { /* ignore */ } }
    }
    for (const c of pngChunks(u8)) { const x = await pngXmp(u8, c); if (x) return xmpDate(x.text); }
    return null;
  }

  async function pngEdit(file, u8, tm) {
    const chunks = pngChunks(u8);
    if (!chunks.length || chunks[0].type !== 'IHDR') throw new DFError('PNG 파일이 손상되었어요.');
    const patches = [];
    const ex = chunks.find(c => c.type === 'eXIf');
    const r = editTiff(ex ? u8.subarray(ex.data, ex.dataEnd) : null, tm);
    let tiff = r.bytes;
    if (r.patches) { tiff = u8.slice(ex.data, ex.dataEnd); for (const p of r.patches) tiff.set(p.bytes, p.pos); }
    const chunk = pngChunk('eXIf', tiff);
    if (ex) patches.push({ start: ex.start, end: ex.end, bytes: chunk });
    else patches.push({ start: chunks[0].end, end: chunks[0].end, bytes: chunk });
    for (const c of chunks) {
      const x = await pngXmp(u8, c);
      if (!x) continue;
      const next = editXmp(x.text, tm);
      if (next !== x.text) patches.push({ start: c.start, end: c.end, bytes: pngChunk('iTXt', concat([x.head, utf8(next)])) });
    }
    return assemble(file, patches, 'image/png');
  }

  // ---------- ISOBMFF helpers ----------
  function readBoxes(u8, start, end) {
    const out = []; let p = start;
    while (p + 8 <= end) {
      let size = u32BE(u8, p), hdr = 8;
      const type = str4(u8, p + 4);
      if (size === 1) { size = u64BE(u8, p + 8); hdr = 16; } else if (size === 0) size = end - p;
      if (size < hdr || p + size > end) break;
      out.push({ type, start: p, payload: p + hdr, end: p + size });
      p += size;
    }
    return out;
  }
  function makeBox(type, parts) {
    const body = concat(parts);
    const t = typeof type === 'string' ? latin1(type) : type;
    if (body.length + 8 > 0xFFFFFFFF) return concat([bytesN(4, 1), t, bytesN(8, body.length + 16), body]);
    return concat([bytesN(4, body.length + 8), t, body]);
  }

  // ---------- HEIF / HEIC ----------
  function heifItems(u8) {
    const meta = readBoxes(u8, 0, u8.length).find(b => b.type === 'meta');
    if (!meta) throw new DFError('HEIC 파일 구조를 읽을 수 없어요.');
    const kids = readBoxes(u8, meta.payload + 4, meta.end);
    const iinf = kids.find(b => b.type === 'iinf'), iloc = kids.find(b => b.type === 'iloc');
    if (!iinf || !iloc) throw new DFError('HEIC 파일 구조를 읽을 수 없어요.');

    const items = {};
    const iv = u8[iinf.payload];
    const infes = readBoxes(u8, iinf.payload + 4 + (iv === 0 ? 2 : 4), iinf.end).filter(b => b.type === 'infe');
    for (const b of infes) {
      const v = u8[b.payload]; let q = b.payload + 4;
      if (v < 2) continue;
      const id = v === 2 ? u16BE(u8, q) : u32BE(u8, q); q += (v === 2 ? 2 : 4) + 2;
      const type = str4(u8, q); q += 4;
      let contentType = '';
      if (type === 'mime') { q = u8.indexOf(0, q) + 1; const e = u8.indexOf(0, q); contentType = str(u8, q, e - q); }
      items[id] = { id, type, contentType };
    }

    const v = u8[iloc.payload]; let q = iloc.payload + 4;
    const offSize = u8[q] >> 4, lenSize = u8[q] & 15, baseSize = u8[q + 1] >> 4;
    const idxSize = v === 1 || v === 2 ? u8[q + 1] & 15 : 0;
    q += 2;
    const count = v < 2 ? u16BE(u8, q) : u32BE(u8, q); q += v < 2 ? 2 : 4;
    for (let i = 0; i < count; i++) {
      const id = v < 2 ? u16BE(u8, q) : u32BE(u8, q); q += v < 2 ? 2 : 4;
      let method = 0;
      if (v === 1 || v === 2) { method = u16BE(u8, q) & 15; q += 2; }
      q += 2; // data_reference_index
      const basePos = q, base = readN(u8, q, baseSize); q += baseSize;
      const ec = u16BE(u8, q); q += 2;
      const extents = [];
      for (let j = 0; j < ec; j++) {
        q += idxSize;
        const offPos = q, off = readN(u8, q, offSize); q += offSize;
        const lenPos = q, len = readN(u8, q, lenSize); q += lenSize;
        extents.push({ offPos, off, lenPos, len });
      }
      if (items[id]) Object.assign(items[id], { method, basePos, base, extents });
    }
    const loc = it => {
      if (!it || !it.extents || it.method !== 0 || it.extents.length !== 1) return null;
      const e = it.extents[0];
      return { start: it.base + e.off, end: it.base + e.off + e.len };
    };
    const list = Object.values(items);
    const exif = list.find(i => i.type === 'Exif');
    const xmp = list.find(i => i.type === 'mime' && /rdf\+xml/.test(i.contentType));
    return { offSize, lenSize, baseSize, exif, xmp, exifLoc: loc(exif), xmpLoc: loc(xmp) };
  }

  function heifRead(u8) {
    const h = heifItems(u8);
    if (h.exifLoc) {
      const ts = h.exifLoc.start + 4 + u32BE(u8, h.exifLoc.start);
      try { const d = tiffDate(parseTiff(u8.subarray(ts, h.exifLoc.end))); if (d) return d; } catch (e) { /* ignore */ }
    }
    return h.xmpLoc ? xmpDate(new TextDecoder().decode(u8.subarray(h.xmpLoc.start, h.xmpLoc.end))) : null;
  }

  function heifEdit(file, u8, tm, type) {
    const h = heifItems(u8);
    if (!h.exifLoc) throw new DFError('이 HEIC 파일에는 날짜 정보를 넣을 자리가 없어요.');
    const patches = [];
    const appended = [];
    let tail = u8.length;
    // Moves an item's data to a new mdat box at the end of the file and points iloc at it.
    const relocate = (item, bytes) => {
      const pos = tail + 8;
      const e = item.extents[0];
      if (h.offSize) patches.push({ start: e.offPos, end: e.offPos + h.offSize, bytes: bytesN(h.offSize, pos - item.base) });
      else if (h.baseSize) patches.push({ start: item.basePos, end: item.basePos + h.baseSize, bytes: bytesN(h.baseSize, pos) });
      else throw new DFError('이 HEIC 파일은 지원하지 않는 구조예요.');
      if (!h.lenSize) throw new DFError('이 HEIC 파일은 지원하지 않는 구조예요.');
      patches.push({ start: e.lenPos, end: e.lenPos + h.lenSize, bytes: bytesN(h.lenSize, bytes.length) });
      const box = makeBox('mdat', [bytes]);
      appended.push(box);
      tail += box.length;
    };

    const ts = h.exifLoc.start + 4 + u32BE(u8, h.exifLoc.start);
    const r = editTiff(u8.subarray(ts, h.exifLoc.end), tm);
    if (r.patches) for (const p of r.patches) patches.push({ start: ts + p.pos, end: ts + p.pos + p.bytes.length, bytes: p.bytes });
    else relocate(h.exif, concat([bytesN(4, 6), Uint8Array.from(EXIF_HDR), r.bytes]));

    if (h.xmpLoc) {
      const text = new TextDecoder().decode(u8.subarray(h.xmpLoc.start, h.xmpLoc.end));
      const next = editXmp(text, tm);
      if (next !== text) {
        const nb = utf8(next);
        if (nb.length === h.xmpLoc.end - h.xmpLoc.start) patches.push({ start: h.xmpLoc.start, end: h.xmpLoc.end, bytes: nb });
        else relocate(h.xmp, nb);
      }
    }
    if (appended.length) patches.push({ start: u8.length, end: u8.length, bytes: concat(appended) });
    return assemble(file, patches, type);
  }

  // ---------- MOV / MP4 ----------
  async function readAt(file, a, b) { return new Uint8Array(await file.slice(a, b).arrayBuffer()); }

  async function topBoxes(file) {
    const out = []; let p = 0;
    while (p + 8 <= file.size) {
      const h = await readAt(file, p, Math.min(p + 16, file.size));
      let size = u32BE(h, 0), hdr = 8;
      if (size === 1) { size = u64BE(h, 8); hdr = 16; } else if (size === 0) size = file.size - p;
      if (size < hdr) break;
      out.push({ type: str4(h, 4), start: p, end: Math.min(p + size, file.size) });
      p += size;
    }
    return out;
  }

  const MOOV_CONTAINERS = new Set(['moov', 'trak', 'mdia', 'minf', 'udta', 'edts', 'dinf']);
  const QT_DATE_KEY = 'com.apple.quicktime.creationdate';
  const DAY = '\xa9day';

  function metaChildrenStart(u8, b) {
    // QuickTime-style meta has no version/flags; ISO meta does.
    if (str4(u8, b.payload + 4) === 'hdlr' || u32BE(u8, b.payload) !== 0) return b.payload;
    return b.payload + 4;
  }
  function metaKeys(u8, kids) {
    const names = {};
    const keys = kids.find(k => k.type === 'keys');
    if (keys) {
      let q = keys.payload + 4;
      const n = u32BE(u8, q); q += 4;
      for (let i = 1; i <= n && q + 8 <= keys.end; i++) { const s = u32BE(u8, q); names[i] = str(u8, q + 8, s - 8); q += s; }
    }
    return names;
  }

  // Walks moov and returns what it finds (read) or a rebuilt moov (edit).
  function walkMoov(u8, moov, ctx) {
    function box(b, parent) {
      const raw = u8.subarray(b.start, b.end);
      const t = b.type;
      if (t === 'mvhd' || t === 'tkhd' || t === 'mdhd') {
        const o = b.payload - b.start, v = raw[o];
        if (t === 'mvhd' && ctx.read) ctx.found.mvhd = v === 1 ? u64BE(raw, o + 4) : u32BE(raw, o + 4);
        if (ctx.read) return raw;
        const c = raw.slice();
        if (v === 1) { c.set(bytesN(8, ctx.qtSecs), o + 4); c.set(bytesN(8, ctx.qtSecs), o + 12); }
        else { c.set(bytesN(4, ctx.qtSecs), o + 4); c.set(bytesN(4, ctx.qtSecs), o + 8); }
        return c;
      }
      if (t === 'meta') {
        const cs = metaChildrenStart(u8, b);
        const kids = readBoxes(u8, cs, b.end);
        const names = metaKeys(u8, kids);
        const parts = kids.map(k => k.type === 'ilst' ? ilst(k, names) : u8.subarray(k.start, k.end));
        return ctx.read ? raw : makeBox('meta', [u8.subarray(b.payload, cs), ...parts]);
      }
      if (t === DAY && parent === 'udta') {
        // QuickTime text record: u16 length, u16 language, text
        if (str4(u8, b.payload + 4) === 'data') return dataItem(b, DAY);
        const len = u16BE(u8, b.payload);
        if (ctx.read) { ctx.found.day = ctx.found.day || str(u8, b.payload + 4, len); return raw; }
        const txt = utf8(ctx.iso);
        return makeBox(raw.subarray(4, 8), [bytesN(2, txt.length), u8.subarray(b.payload + 2, b.payload + 4), txt]);
      }
      if (MOOV_CONTAINERS.has(t)) {
        const kids = readBoxes(u8, b.payload, b.end);
        const parts = kids.map(k => box(k, t));
        if (t === 'moov' && !ctx.read && !ctx.hasQtKey && !kids.some(k => k.type === 'meta')) parts.push(newQtMeta(ctx.qtIso));
        return ctx.read ? raw : makeBox(raw.subarray(4, 8), parts);
      }
      return raw;
    }
    function dataItem(item, name) {
      const raw = u8.subarray(item.start, item.end);
      const parts = readBoxes(u8, item.payload, item.end).map(d => {
        if (d.type !== 'data') return u8.subarray(d.start, d.end);
        if (ctx.read) {
          const v = new TextDecoder().decode(u8.subarray(d.payload + 8, d.end));
          if (name === QT_DATE_KEY) ctx.found.qt = v; else ctx.found.day = ctx.found.day || v;
          return null;
        }
        return makeBox('data', [u8.subarray(d.payload, d.payload + 8), utf8(name === QT_DATE_KEY ? ctx.qtIso : ctx.iso)]);
      });
      if (name === QT_DATE_KEY) ctx.hasQtKey = true;
      return ctx.read ? raw : makeBox(raw.subarray(4, 8), parts);
    }
    function ilst(b, names) {
      const parts = readBoxes(u8, b.payload, b.end).map(item => {
        const name = item.type === DAY ? DAY : names[u32BE(u8, item.start + 4)];
        return name === QT_DATE_KEY || name === DAY ? dataItem(item, name) : u8.subarray(item.start, item.end);
      });
      return ctx.read ? null : makeBox('ilst', parts);
    }
    return box({ type: 'moov', start: moov.start, payload: moov.start + (u32BE(u8, moov.start) === 1 ? 16 : 8), end: moov.end }, null);
  }

  function newQtMeta(value) {
    const hdlr = makeBox('hdlr', [new Uint8Array(8), latin1('mdta'), new Uint8Array(12), new Uint8Array(1)]);
    const keys = makeBox('keys', [new Uint8Array(4), bytesN(4, 1), makeBox('mdta', [latin1(QT_DATE_KEY)])]);
    const data = makeBox('data', [bytesN(4, 1), new Uint8Array(4), utf8(value)]);
    const ilst = makeBox('ilst', [makeBox(bytesN(4, 1), [data])]);
    return makeBox('meta', [hdlr, keys, ilst]);
  }

  // Adds delta to chunk offsets that pointed past the old moov.
  function shiftChunkOffsets(u8, after, delta) {
    const walk = (s, e) => {
      for (const b of readBoxes(u8, s, e)) {
        if (['moov', 'trak', 'mdia', 'minf', 'stbl'].includes(b.type)) walk(b.payload, b.end);
        else if (b.type === 'stco' || b.type === 'co64') {
          const w = b.type === 'stco' ? 4 : 8;
          const n = u32BE(u8, b.payload + 4);
          for (let i = 0, q = b.payload + 8; i < n; i++, q += w) {
            const v = readN(u8, q, w);
            if (v >= after) u8.set(bytesN(w, v + delta), q);
          }
        }
      }
    };
    walk(0, u8.length);
  }

  async function videoLoad(file) {
    const boxes = await topBoxes(file);
    const moov = boxes.find(b => b.type === 'moov');
    if (!moov) throw new DFError('영상 파일 구조를 읽을 수 없어요.');
    const u8 = await readAt(file, moov.start, moov.end);
    return { boxes, moov, u8, local: { type: 'moov', start: 0, end: u8.length } };
  }

  async function videoRead(file) {
    const { u8, local } = await videoLoad(file);
    const ctx = { read: true, found: {} };
    walkMoov(u8, local, ctx);
    return parseIsoDate(ctx.found.qt) || fromUtcSeconds(ctx.found.mvhd ? ctx.found.mvhd - QT_EPOCH : 0) || parseIsoDate(ctx.found.day);
  }

  async function videoEdit(file, tm, type) {
    const { moov, u8, local } = await videoLoad(file);
    const ctx = { read: false, qtSecs: Math.floor(utcMillis(tm) / 1000) + QT_EPOCH, iso: isoDate(tm), qtIso: isoDate(tm, false), hasQtKey: false };
    // First pass learns whether the creation-date key exists, second pass writes.
    const probe = { read: true, found: {} };
    walkMoov(u8, local, probe);
    ctx.hasQtKey = probe.found.qt != null;
    const out = walkMoov(u8, local, ctx);
    const delta = out.length - u8.length;
    if (delta) shiftChunkOffsets(out, moov.end, delta);
    return assemble(file, [{ start: moov.start, end: moov.end, bytes: out }], type);
  }

  // ---------- detection & API ----------
  const HEIF_BRANDS = ['heic', 'heix', 'heim', 'heis', 'hevc', 'hevx', 'mif1', 'msf1', 'avif', 'avis'];

  async function detect(file) {
    const h = await readAt(file, 0, 64);
    if (h[0] === 0xFF && h[1] === 0xD8) return { format: 'jpeg', kind: 'photo', mime: 'image/jpeg' };
    if (startsWith(h, 0, [0x89, 0x50, 0x4E, 0x47])) return { format: 'png', kind: 'photo', mime: 'image/png' };
    if (str4(h, 4) === 'ftyp') {
      const size = u32BE(h, 0);
      const brands = [str4(h, 8)];
      for (let o = 16; o + 4 <= Math.min(size, h.length); o += 4) brands.push(str4(h, o));
      if (HEIF_BRANDS.includes(brands[0]) || (brands.includes('mif1') && !brands.includes('qt  ')))
        return { format: 'heif', kind: 'photo', mime: brands[0] === 'avif' ? 'image/avif' : 'image/heic' };
      return { format: 'video', kind: 'video', mime: brands[0] === 'qt  ' ? 'video/quicktime' : 'video/mp4' };
    }
    if (['moov', 'mdat', 'wide', 'free', 'skip'].includes(str4(h, 4))) return { format: 'video', kind: 'video', mime: 'video/quicktime' };
    if (str4(h, 0) === 'RIFF' && str4(h, 8) === 'WEBP') throw new DFError('WebP는 아직 지원하지 않아요. JPEG, PNG, HEIC 사진을 올려 주세요.');
    if (str(h, 0, 3) === 'GIF') throw new DFError('GIF는 날짜 정보를 담을 수 없는 형식이에요.');
    throw new DFError('지원하지 않는 파일 형식이에요.');
  }

  async function readDate(file) {
    const info = await detect(file);
    if (info.format === 'video') return videoRead(file);
    const u8 = new Uint8Array(await file.arrayBuffer());
    if (info.format === 'jpeg') return jpegRead(u8);
    if (info.format === 'png') return pngRead(u8);
    return heifRead(u8);
  }

  async function setDate(file, tm) {
    const info = await detect(file);
    if (info.format === 'video') return videoEdit(file, tm, file.type || info.mime);
    const u8 = new Uint8Array(await file.arrayBuffer());
    if (info.format === 'jpeg') return jpegEdit(file, u8, tm);
    if (info.format === 'png') return pngEdit(file, u8, tm);
    return heifEdit(file, u8, tm, file.type || info.mime);
  }

  global.DateFix = { detect, readDate, setDate, DFError, _test: { parseTiff, serializeTiff, isoDate, exifDate } };
})(typeof window !== 'undefined' ? window : globalThis);
