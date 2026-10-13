"use strict";

const $ = selector => document.querySelector(selector);
const $$ = selector => Array.from(document.querySelectorAll(selector));
const MAX_FILE_SIZE = 128 * 1024 * 1024;
const CASE_KEY = "tracelab.case.v2";
let primaryFile = null;
let primaryRecord = null;
let analysisToken = 0;
let activeMd5Worker = null;
let packets = [];
let logs = [];
let timeline = [];
let caseData = loadCase();
let osintNotes = [];

function el(tag, text, className) {
  const node = document.createElement(tag);
  if (text !== undefined) node.textContent = String(text);
  if (className) node.className = className;
  return node;
}
function notify(message) {
  const toast = $("#toast");
  toast.textContent = message;
  toast.classList.add("show");
  clearTimeout(notify.timer);
  notify.timer = setTimeout(() => toast.classList.remove("show"), 2600);
}
function formatBytes(bytes) {
  if (!Number.isFinite(bytes)) return "Unknown";
  if (bytes === 0) return "0 bytes";
  const units = ["bytes", "KB", "MB", "GB", "TB"];
  const index = Math.min(Math.floor(Math.log(bytes) / Math.log(1024)), units.length - 1);
  return `${(bytes / Math.pow(1024, index)).toFixed(index ? 2 : 0)} ${units[index]}`;
}
function hex(bytes) { return Array.from(bytes, byte => byte.toString(16).padStart(2, "0")).join(""); }
function shortHash(hash) { return hash.length > 20 ? `${hash.slice(0, 12)} … ${hash.slice(-8)}` : hash; }
function csv(rows) {
  return rows.map(row => row.map(value => `"${String(value ?? "").replace(/"/g, '""')}"`).join(",")).join("\r\n");
}
function download(name, content, type = "application/json") {
  const url = URL.createObjectURL(new Blob([content], { type }));
  const anchor = el("a");
  anchor.href = url; anchor.download = name; anchor.click();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}
function loadCase() {
  try {
    const saved = JSON.parse(localStorage.getItem(CASE_KEY) || "null");
    if (saved && saved.schemaVersion === 2 && Array.isArray(saved.evidence) && Array.isArray(saved.audit) &&
        saved.evidence.every(item => item && typeof item.id === "string" && typeof item.name === "string" && Number.isFinite(item.size)) &&
        saved.audit.every(item => item && typeof item.time === "string" && typeof item.action === "string" && typeof item.details === "string") &&
        (saved.timeline === undefined || (Array.isArray(saved.timeline) && saved.timeline.every(item => item && typeof item.description === "string" && (item.epoch === null || Number.isFinite(item.epoch) && Math.abs(item.epoch) <= 8640000000000000))))) return saved;
  } catch (error) { console.warn("Saved TraceLab case could not be loaded.", error); }
  return { schemaVersion: 2, caseId: "", title: "", notes: "", evidence: [], audit: [], timeline: [] };
}
function audit(action, details) {
  caseData.audit.unshift({ time: new Date().toISOString(), action, details: String(details || "") });
  caseData.audit = caseData.audit.slice(0, 500);
}
function saveCaseData(action, details) {
  caseData.timeline = timeline;
  audit(action, details);
  try {
    localStorage.setItem(CASE_KEY, JSON.stringify(caseData));
    $("#storageStatus").textContent = "Case data saved in this browser’s local storage. It is not encrypted or tamper-proof.";
  } catch (error) {
    $("#storageStatus").textContent = `Could not save case data: ${error.message}`;
    notify("Case data could not be saved.");
  }
  renderCase(false);
}
function renderCase(updateFields = true) {
  if (updateFields) {
    $("#caseId").value = caseData.caseId || "";
    $("#caseTitle").value = caseData.title || "";
    $("#caseNotes").value = caseData.notes || "";
  }
  const evidence = $("#evidenceRows"); evidence.replaceChildren();
  for (const item of caseData.evidence) {
    const row = el("tr");
    [item.id, item.name, formatBytes(item.size), item.sha256 || "Not calculated", item.type, item.addedAt].forEach(value => row.append(el("td", value)));
    evidence.append(row);
  }
  const auditBody = $("#auditRows"); auditBody.replaceChildren();
  for (const item of caseData.audit) {
    const row = el("tr");
    [item.time, item.action, item.details].forEach(value => row.append(el("td", value)));
    auditBody.append(row);
  }
}

function md5(buffer) {
  const input = new Uint8Array(buffer);
  const length = input.length;
  const paddedLength = Math.ceil((length + 9) / 64) * 64;
  const data = new Uint8Array(paddedLength);
  data.set(input); data[length] = 0x80;
  const view = new DataView(data.buffer);
  const bits = length * 8;
  view.setUint32(paddedLength - 8, bits >>> 0, true);
  view.setUint32(paddedLength - 4, Math.floor(bits / 0x100000000), true);
  const shifts = [7,12,17,22,7,12,17,22,7,12,17,22,7,12,17,22,5,9,14,20,5,9,14,20,5,9,14,20,5,9,14,20,4,11,16,23,4,11,16,23,4,11,16,23,4,11,16,23,6,10,15,21,6,10,15,21,6,10,15,21,6,10,15,21];
  const constants = Array.from({ length: 64 }, (_, i) => Math.floor(Math.abs(Math.sin(i + 1)) * 0x100000000) >>> 0);
  let a0 = 0x67452301, b0 = 0xefcdab89, c0 = 0x98badcfe, d0 = 0x10325476;
  for (let offset = 0; offset < paddedLength; offset += 64) {
    const words = new Uint32Array(16);
    for (let i = 0; i < 16; i++) words[i] = view.getUint32(offset + i * 4, true);
    let a = a0, b = b0, c = c0, d = d0;
    for (let i = 0; i < 64; i++) {
      let f, g;
      if (i < 16) { f = (b & c) | (~b & d); g = i; }
      else if (i < 32) { f = (d & b) | (~d & c); g = (5 * i + 1) % 16; }
      else if (i < 48) { f = b ^ c ^ d; g = (3 * i + 5) % 16; }
      else { f = c ^ (b | ~d); g = (7 * i) % 16; }
      const sum = (a + f + constants[i] + words[g]) >>> 0;
      const next = (b + ((sum << shifts[i]) | (sum >>> (32 - shifts[i])))) >>> 0;
      a = d; d = c; c = b; b = next;
    }
    a0 = (a0 + a) >>> 0; b0 = (b0 + b) >>> 0; c0 = (c0 + c) >>> 0; d0 = (d0 + d) >>> 0;
  }
  const result = new Uint8Array(16), output = new DataView(result.buffer);
  [a0, b0, c0, d0].forEach((word, i) => output.setUint32(i * 4, word, true));
  return hex(result);
}
function cancelMd5Worker() {
  if (!activeMd5Worker) return;
  const worker = activeMd5Worker;
  activeMd5Worker = null;
  worker.terminate();
  if (worker.cancel) worker.cancel();
}
function entropyStats(bytes) {
  const entropy = segment => {
    if (!segment.length) return 0;
    const counts = new Uint32Array(256);
    for (const byte of segment) counts[byte]++;
    let result = 0;
    for (const count of counts) if (count) { const p = count / segment.length; result -= p * Math.log2(p); }
    return result;
  };
  const overall = entropy(bytes), count = Math.min(32, bytes.length), regions = [];
  for (let i = 0; i < count; i++) {
    const start = Math.floor(i * bytes.length / count), end = Math.floor((i + 1) * bytes.length / count);
    regions.push({ start, end, value: entropy(bytes.subarray(start, end)) });
  }
  return { overall, regions };
}
function renderEntropy(stats, byteLength) {
  $("#entropyOverall").textContent = `Overall entropy: ${stats.overall.toFixed(4)} bits/byte · ${byteLength.toLocaleString()} bytes`;
  const chart = $("#entropyChart"); chart.replaceChildren();
  if (!byteLength) { chart.append(el("p", "Empty file has no byte distribution to graph.", "status")); return; }
  for (const region of stats.regions) {
    const bar = el("div", undefined, "entropy-bar");
    bar.style.height = `${Math.max(2, region.value / 8 * 100)}%`;
    bar.title = `Bytes ${region.start.toLocaleString()}–${(region.end - 1).toLocaleString()}: ${region.value.toFixed(3)} bits/byte`;
    chart.append(bar);
  }
}
function analyzeBytesInWorker(buffer) {
  if (typeof Worker === "undefined") return Promise.resolve().then(() => ({ hash: md5(buffer), entropy: entropyStats(new Uint8Array(buffer)) }));
  let url;
  try {
    const workerSource = `const hex = bytes => Array.from(bytes, byte => byte.toString(16).padStart(2, "0")).join("");\n${md5.toString()}\n${entropyStats.toString()}\nself.onmessage = event => { try { const bytes = new Uint8Array(event.data); self.postMessage({ hash: md5(event.data), entropy: entropyStats(bytes) }); } catch (error) { self.postMessage({ error: error.message }); } };`;
    url = URL.createObjectURL(new Blob([workerSource], { type: "text/javascript" }));
    const worker = new Worker(url);
    return new Promise((resolve, reject) => {
      let settled = false;
      const finish = (error, value) => {
        if (settled) return;
        settled = true;
        worker.terminate(); URL.revokeObjectURL(url);
        if (activeMd5Worker === worker) activeMd5Worker = null;
        error ? reject(error) : resolve(value);
      };
      worker.cancel = () => finish(new Error("MD5 calculation cancelled."));
      worker.onmessage = event => event.data?.error ? finish(new Error(event.data.error)) : finish(null, event.data);
      worker.onerror = event => finish(new Error(event.message || "MD5 worker failed."));
      activeMd5Worker = worker;
      try { worker.postMessage(buffer, [buffer]); }
      catch (error) { finish(error); }
    });
  } catch (error) {
    if (url) URL.revokeObjectURL(url);
    return Promise.resolve().then(() => md5(buffer));
  }
}

const SIGNATURES = [
  { label: "PDF", bytes: [0x25,0x50,0x44,0x46], rule: "25 50 44 46 at offset 0" },
  { label: "PNG", bytes: [0x89,0x50,0x4e,0x47,0x0d,0x0a,0x1a,0x0a], rule: "89 50 4E 47 0D 0A 1A 0A at offset 0" },
  { label: "JPEG", bytes: [0xff,0xd8,0xff], rule: "FF D8 FF at offset 0" },
  { label: "GIF", bytes: [0x47,0x49,0x46,0x38], rule: "GIF8 at offset 0" },
  { label: "BMP", bytes: [0x42,0x4d], rule: "BM at offset 0" },
  { label: "TIFF little-endian", bytes: [0x49,0x49,0x2a,0x00], rule: "49 49 2A 00 at offset 0" },
  { label: "TIFF big-endian", bytes: [0x4d,0x4d,0x00,0x2a], rule: "4D 4D 00 2A at offset 0" },
  { label: "ZIP / OOXML container", bytes: [0x50,0x4b,0x03,0x04], rule: "50 4B 03 04 at offset 0" },
  { label: "ZIP empty archive", bytes: [0x50,0x4b,0x05,0x06], rule: "50 4B 05 06 at offset 0" },
  { label: "GZIP", bytes: [0x1f,0x8b], rule: "1F 8B at offset 0" },
  { label: "7-Zip", bytes: [0x37,0x7a,0xbc,0xaf,0x27,0x1c], rule: "37 7A BC AF 27 1C at offset 0" },
  { label: "RAR", bytes: [0x52,0x61,0x72,0x21,0x1a,0x07], rule: "52 61 72 21 1A 07 at offset 0" },
  { label: "ELF executable", bytes: [0x7f,0x45,0x4c,0x46], rule: "7F 45 4C 46 at offset 0" },
  { label: "Windows PE / DOS executable", bytes: [0x4d,0x5a], rule: "4D 5A at offset 0 (PE header not validated)" },
  { label: "SQLite database", bytes: Array.from(new TextEncoder().encode("SQLite format 3\u0000")), rule: "SQLite format 3 NUL at offset 0" },
  { label: "WAV / RIFF container", bytes: [0x52,0x49,0x46,0x46], rule: "RIFF at offset 0" },
  { label: "MP3 (ID3)", bytes: [0x49,0x44,0x33], rule: "ID3 at offset 0" },
  { label: "FLAC audio", bytes: [0x66,0x4c,0x61,0x43], rule: "fLaC at offset 0" },
  { label: "Ogg media", bytes: [0x4f,0x67,0x67,0x53], rule: "OggS at offset 0" },
  { label: "Windows Script (batch / command)", bytes: [0x40,0x65,0x63,0x68,0x6f], rule: "ASCII @echo prefix (case-insensitive, heuristic)" }
];
function detectSignature(bytes) {
  if (bytes.length >= 12 && bytes[0] === 0x52 && bytes[1] === 0x49 && bytes[2] === 0x46 && bytes[3] === 0x46 && bytes[8] === 0x57 && bytes[9] === 0x45 && bytes[10] === 0x42 && bytes[11] === 0x50)
    return { label: "WebP", rule: "RIFF at offset 0 and WEBP at offset 8", observed: hex(bytes.slice(0, 12)).match(/.{1,2}/g).join(" "), conclusive: true };
  if (bytes.length >= 12 && bytes[4] === 0x66 && bytes[5] === 0x74 && bytes[6] === 0x79 && bytes[7] === 0x70)
    return { label: "ISO Base Media container (MP4 family)", rule: "ftyp brand marker at offset 4; exact format not established", observed: hex(bytes.slice(0, 12)).match(/.{1,2}/g).join(" "), conclusive: false };
  for (const sig of SIGNATURES) {
    if (sig.label.startsWith("WAV")) {
      if (bytes.length >= 12 && bytes[8] === 0x57 && bytes[9] === 0x41 && bytes[10] === 0x56 && bytes[11] === 0x45)
        return { label: "WAV audio", rule: "RIFF at offset 0 and WAVE at offset 8", observed: hex(bytes.slice(0, 12)).match(/.{1,2}/g).join(" "), conclusive: true };
      continue;
    }
    const matches = sig.bytes.every((value, i) => bytes[i] === value);
    if (matches) return { label: sig.label, rule: sig.rule, observed: hex(bytes.slice(0, sig.bytes.length)).match(/.{1,2}/g)?.join(" ") || "None", conclusive: true };
  }
  const ascii = new TextDecoder().decode(bytes.slice(0, 128)).trimStart().toLowerCase();
  if (ascii.startsWith("#!")) return { label: "Script (shebang)", rule: "Text begins with #! (heuristic)", observed: hex(bytes.slice(0, 16)).match(/.{1,2}/g)?.join(" ") || "None", conclusive: false };
  if (ascii.startsWith("@echo")) return { label: "Windows batch script (possible)", rule: "Text begins with @echo (case-insensitive heuristic)", observed: hex(bytes.slice(0, 8)).match(/.{1,2}/g)?.join(" ") || "None", conclusive: false };
  return { label: bytes.length ? "Inconclusive / unknown signature" : "Empty file — no leading bytes", rule: "No supported rule matched the leading bytes", observed: bytes.length ? hex(bytes.slice(0, 16)).match(/.{1,2}/g).join(" ") : "(empty)", conclusive: false };
}
function setMetadata(file, signature, bytes) {
  const extension = file.name.includes(".") ? `.${file.name.split(".").pop()}` : "(none)";
  const rows = [
    ["File name", file.name], ["Size", `${formatBytes(file.size)} (${file.size.toLocaleString()} bytes)`],
    ["Browser MIME", file.type || "Not supplied"], ["Extension", extension],
    ["Last modified", file.lastModified ? new Date(file.lastModified).toLocaleString() : "Not supplied (not capture time)"],
    ["Observed signature", signature.label], ["Signature rule", signature.rule], ["Observed leading bytes", signature.observed]
  ];
  if (signature.label.includes("PNG") && bytes.length >= 24) rows.push(["Image dimensions", `${new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength).getUint32(16)} × ${new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength).getUint32(20)} px`]);
  const extensionFormats = { ".pdf": "PDF", ".png": "PNG", ".jpg": "JPEG", ".jpeg": "JPEG", ".gif": "GIF", ".webp": "WebP", ".bmp": "BMP", ".tif": "TIFF", ".tiff": "TIFF", ".zip": "ZIP", ".gz": "GZIP", ".7z": "7-Zip", ".rar": "RAR", ".exe": "Windows PE", ".sqlite": "SQLite", ".db": "SQLite" };
  const expected = extensionFormats[extension.toLowerCase()];
  if (expected && signature.conclusive && !signature.label.toLowerCase().includes(expected.toLowerCase()))
    rows.push(["Extension conflict", `Extension suggests ${expected}; leading bytes suggest ${signature.label}. Extension is user-controlled and not proof.`]);
  if (expected && !signature.conclusive)
    rows.push(["Extension inconclusive", `Extension suggests ${expected}, but no supported signature confirmed it.`]);
  const mimeHints = { "application/pdf": "PDF", "image/png": "PNG", "image/jpeg": "JPEG", "image/gif": "GIF", "image/webp": "WebP", "image/bmp": "BMP", "application/zip": "ZIP", "application/x-gzip": "GZIP", "application/x-7z-compressed": "7-Zip", "application/vnd.sqlite3": "SQLite" };
  const mimeHint = mimeHints[file.type.toLowerCase()];
  if (mimeHint && signature.conclusive && !signature.label.toLowerCase().includes(mimeHint.toLowerCase()))
    rows.push(["MIME conflict", `Browser MIME suggests ${mimeHint}; leading bytes suggest ${signature.label}. Browser MIME is not authoritative.`]);
  else if (file.type.toLowerCase() === "text/plain" && signature.conclusive)
    rows.push(["MIME conflict", `Browser reports text/plain; leading bytes match ${signature.label}. MIME is not authoritative.`]);
  const container = $("#metadata"); container.replaceChildren();
  for (const [key, value] of rows) {
    const row = el("div", undefined, "meta-row");
    row.append(el("span", key, "meta-key"), el("span", value, "meta-value")); container.append(row);
  }
}
async function inspectFile(file) {
  cancelMd5Worker();
  const token = ++analysisToken;
  primaryFile = file; primaryRecord = null;
  $("#dropTitle").textContent = file.name;
  $("#dropSubtitle").textContent = `${formatBytes(file.size)} · ${file.type || "browser MIME unavailable"} · selected locally`;
  $("#fileSummary").textContent = `Selected ${file.name}. Hashing entire file in memory; cancel by choosing another file or Clear.`;
  $("#hashStatus").textContent = "Reading bytes for whole-file digests; progress is indeterminate.";
  $("#progressBar").classList.add("indeterminate");
  $$(".hash-card").forEach(card => { card.querySelector(".hash-value").textContent = "Calculating…"; card.querySelector(".status").textContent = "Processing"; card.dataset.full = ""; });
  $("#metadata").replaceChildren(el("p", "Reading file properties…", "empty"));
  $("#textPreview").value = "";
  $("#entropyOverall").textContent = "Calculating entropy…";
  $("#entropyChart").replaceChildren();
  $("#imagePreview").hidden = true; $("#imagePreview").removeAttribute("src");
  if (file.size > MAX_FILE_SIZE) {
    setHashesError(`File exceeds ${formatBytes(MAX_FILE_SIZE)} browser-analysis limit.`);
    $("#fileSummary").textContent = `${file.name}: file is too large for this memory-limited build.`;
    $("#progressBar").classList.remove("indeterminate");
    return;
  }
  try {
    const buffer = await file.arrayBuffer();
    if (token !== analysisToken) return;
    const bytes = new Uint8Array(buffer);
    const signature = detectSignature(bytes.slice(0, 64));
    setMetadata(file, signature, bytes.slice(0, 64));
    $("#textPreview").value = new TextDecoder("utf-8").decode(bytes.slice(0, 32768));
    $("#previewStatus").textContent = `Showing ${formatBytes(Math.min(file.size, 32768))} of ${formatBytes(file.size)} as UTF-8; binary may show replacement characters.`;
    imageInspection(file);
    const digests = {};
    for (const algorithm of ["SHA-256", "SHA-384", "SHA-512"]) {
      try { digests[algorithm] = hex(new Uint8Array(await crypto.subtle.digest(algorithm, buffer))); }
      catch (error) { digests[algorithm] = null; }
      if (token !== analysisToken) return;
    }
    if (signature.label === "PDF") {
      try { pdfBestEffort(buffer); }
      catch (error) { $("#imageInfo").textContent = `PDF signature detected; supplementary byte scan failed: ${error.message}`; }
    }
    let supplementary = null;
    try { supplementary = await analyzeBytesInWorker(buffer); digests.MD5 = supplementary.hash; }
    catch (_) { digests.MD5 = null; }
    if (token !== analysisToken) return;
    if (supplementary) renderEntropy(supplementary.entropy, file.size);
    $$(".hash-card").forEach(card => {
      const value = digests[card.dataset.alg];
      card.querySelector(".status").textContent = value ? "Ready" : "Unsupported";
      card.querySelector(".hash-value").textContent = value ? shortHash(value) : "Unavailable in this browser";
      card.dataset.full = value || "";
    });
    primaryRecord = { name: file.name, size: file.size, mime: file.type || "", lastModified: file.lastModified || null, signature, hashes: digests };
    $("#fileSummary").textContent = `${file.name} · ${formatBytes(file.size)} · analysis complete locally`;
    $("#hashStatus").textContent = "Complete. Hashing required reading the whole file into memory; no incremental hashing or exact progress is available.";
    $("#progressBar").classList.remove("indeterminate");
    renderHex();
  } catch (error) {
    if (token !== analysisToken) return;
    setHashesError(`Read or hash error: ${error.message}`);
    $("#fileSummary").textContent = `Analysis failed: ${error.message}`;
    $("#progressBar").classList.remove("indeterminate");
  }
}
function setHashesError(message) {
  $$(".hash-card").forEach(card => { card.querySelector(".hash-value").textContent = message; card.querySelector(".status").textContent = "Unavailable"; card.dataset.full = ""; });
  $("#hashStatus").textContent = message;
}
function clearFile() {
  cancelMd5Worker();
  analysisToken++; primaryFile = null; primaryRecord = null; $("#fileInput").value = "";
  $("#dropTitle").textContent = "Drop evidence file here";
  $("#dropSubtitle").textContent = "or choose a file · contents remain in this browser tab";
  $("#fileSummary").textContent = "No file selected.";
  $("#hashStatus").textContent = "Choose a file to begin.";
  $("#progressBar").classList.remove("indeterminate");
  $$(".hash-card").forEach(card => { card.querySelector(".hash-value").textContent = "—"; card.querySelector(".status").textContent = "Waiting"; card.dataset.full = ""; });
  $("#metadata").replaceChildren(el("p", "Select a file to inspect properties.", "empty"));
  $("#textPreview").value = ""; $("#entropyChart").replaceChildren(); $("#entropyOverall").textContent = "Select a file to calculate entropy.";
  $("#imagePreview").hidden = true; $("#imagePreview").removeAttribute("src"); $("#imageInfo").textContent = "Select an image file. EXIF extraction is not currently supported.";
  renderHex();
}
function renderHex() {
  const file = primaryFile;
  if (!file) { $("#hexView").textContent = "No file selected."; $("#hexStatus").textContent = "Select a file to view bytes"; return; }
  let offset = Math.max(0, Math.floor(Number($("#offsetInput").value) || 0));
  offset = Math.min(offset, Math.max(0, file.size - 1)); $("#offsetInput").value = offset;
  file.slice(offset, offset + 256).arrayBuffer().then(buffer => {
    if (file !== primaryFile) return;
    const bytes = new Uint8Array(buffer); const lines = [];
    for (let i = 0; i < bytes.length; i += 16) {
      const part = bytes.slice(i, i + 16);
      const hexText = Array.from(part, b => b.toString(16).padStart(2, "0")).join(" ").padEnd(47, " ");
      const ascii = Array.from(part, b => b >= 32 && b <= 126 ? String.fromCharCode(b) : ".").join("");
      lines.push(`${(offset + i).toString(16).padStart(8, "0")}  ${hexText}  ${ascii}`);
    }
    $("#hexView").textContent = lines.join("\n") || "Empty file.";
    $("#hexStatus").textContent = `${bytes.length ? `${offset.toLocaleString()}–${(offset + bytes.length - 1).toLocaleString()}` : "No"} of ${file.size.toLocaleString()} bytes`;
  }).catch(error => { $("#hexView").textContent = `Could not read bytes: ${error.message}`; });
}
function imageInspection(file) {
  const preview = $("#imagePreview");
  if (!["image/png", "image/jpeg", "image/gif", "image/webp", "image/bmp"].includes(file.type.toLowerCase())) { $("#imageInfo").textContent = "No supported raster image preview. SVG and other formats are not rendered. EXIF extraction is not supported."; return; }
  const url = URL.createObjectURL(file); preview.src = url; preview.hidden = false;
  preview.onload = () => { if (file !== primaryFile) { URL.revokeObjectURL(url); return; } $("#imageInfo").textContent = `Browser-decoded preview · ${preview.naturalWidth} × ${preview.naturalHeight} px. EXIF/camera/GPS metadata is not parsed.`; URL.revokeObjectURL(url); };
  preview.onerror = () => { URL.revokeObjectURL(url); preview.hidden = true; $("#imageInfo").textContent = "Browser could not safely preview this image; metadata parsing is unsupported."; };
}
function pdfBestEffort(buffer) {
  const text = new TextDecoder("latin1").decode(new Uint8Array(buffer));
  const count = (text.match(/\/Type\s*\/Page\b/g) || []).length;
  $("#imageInfo").textContent = count ? `Basic PDF byte scan found ${count} /Page marker(s); this may be incomplete or inaccurate. No PDF library is bundled.` : "PDF signature detected; reliable metadata/page-tree parsing is not implemented.";
}

async function compareFiles() {
  const other = $("#compareInput").files[0];
  if (!primaryFile || !other) { $("#compareStatus").textContent = "Select both files first."; return; }
  if (primaryFile.size > MAX_FILE_SIZE || other.size > MAX_FILE_SIZE) { $("#compareStatus").textContent = `Both files must be under ${formatBytes(MAX_FILE_SIZE)}.`; return; }
  $("#compareStatus").textContent = "Reading and hashing both complete files…";
  try {
    const [a, b] = await Promise.all([primaryFile.arrayBuffer(), other.arrayBuffer()]);
    const [shaA, shaB] = await Promise.all([crypto.subtle.digest("SHA-256", a), crypto.subtle.digest("SHA-256", b)]);
    const first = hex(new Uint8Array(shaA)), second = hex(new Uint8Array(shaB));
    let byteEqual = primaryFile.size === other.size;
    if (byteEqual) {
      const bytesA = new Uint8Array(a), bytesB = new Uint8Array(b);
      for (let i = 0; i < bytesA.length; i++) if (bytesA[i] !== bytesB[i]) { byteEqual = false; break; }
    }
    const hashesMatch = first === second;
    const typeA = detectSignature(new Uint8Array(a).slice(0, 64)), typeB = detectSignature(new Uint8Array(b).slice(0, 64));
    const byteResult = primaryFile.size !== other.size ? "Not identical: sizes differ" : byteEqual ? "Byte-for-byte equal (exact comparison completed)" : "Not identical: one or more byte values differ";
    const rows = [["Property", "Primary file", "Second file"], ["Name", primaryFile.name, other.name], ["Size", `${primaryFile.size} bytes`, `${other.size} bytes`], ["Browser MIME", primaryFile.type || "Unavailable", other.type || "Unavailable"], ["Signature", typeA.label, typeB.label], ["SHA-256", first, second], ["SHA-256 values", hashesMatch ? "Equal (strong practical evidence; not mathematical proof)" : "Different"], ["Byte-by-byte comparison", byteResult, byteResult]];
    const table = $("#compareTable"); table.replaceChildren();
    for (const values of rows) { const tr = el("tr"); values.forEach((value, i) => tr.append(el(i ? "td" : "th", value))); table.append(tr); }
    $("#compareStatus").textContent = "Comparison complete. Both complete contents were read into memory.";
  } catch (error) { $("#compareStatus").textContent = `Comparison failed: ${error.message}. Requires a secure context for SHA-256.`; }
}

function parsePcap(file) {
  if (file.size > 64 * 1024 * 1024) { $("#pcapStatus").textContent = "Capture exceeds the 64 MiB in-memory parser limit."; return; }
  file.arrayBuffer().then(buffer => {
    const view = new DataView(buffer), bytes = new Uint8Array(buffer);
    if (bytes.length < 24) throw new Error("Capture is shorter than a PCAP global header.");
    const magic = hex(bytes.slice(0, 4));
    const endian = ({ "d4c3b2a1": "le", "a1b2c3d4": "be", "4d3cb2a1": "le", "a1b23c4d": "be" })[magic];
    if (!endian) throw new Error("Unknown header; classic PCAP magic not recognized. PCAPNG is unsupported.");
    const le = endian === "le", major = view.getUint16(4, le), minor = view.getUint16(6, le);
    const linkType = view.getUint32(20, le);
    if (major !== 2 || linkType !== 1) throw new Error(`Unsupported PCAP version ${major}.${minor} or link type ${linkType}; expected Ethernet link type 1.`);
    const parsed = []; let offset = 24, index = 0;
    const fractionDivisor = magic === "4d3cb2a1" || magic === "a1b23c4d" ? 1000000000 : 1000000;
    while (offset < bytes.length) {
      if (parsed.length >= 100000) throw new Error("Capture exceeds the 100,000 packet parsing limit.");
      if (offset + 16 > bytes.length) throw new Error(`Truncated packet header at byte ${offset}.`);
      const sec = view.getUint32(offset, le), fraction = view.getUint32(offset + 4, le);
      const included = view.getUint32(offset + 8, le), original = view.getUint32(offset + 12, le);
      if (included > bytes.length - offset - 16 || included > 16 * 1024 * 1024) throw new Error(`Invalid packet length at packet ${index + 1}.`);
      if (included > original) throw new Error(`Captured length exceeds original length at packet ${index + 1}.`);
      if (fraction >= fractionDivisor) throw new Error(`Invalid timestamp fraction at packet ${index + 1}.`);
      const start = offset + 16, end = start + included;
      const packet = { number: ++index, sec, fraction, fractionDivisor, captured: included, original, offset, observedHex: hex(bytes.slice(start, Math.min(end, start + 64))).match(/.{1,2}/g)?.join(" ") || "(empty)", protocol: "Other / unsupported", src: "—", dst: "—", ports: "" };
      if (included >= 14) {
        let ipOffset = start + 14, etherType = view.getUint16(start + 12);
        if (etherType === 0x8100 && included >= 18) { etherType = view.getUint16(start + 16); ipOffset += 4; }
        if (etherType === 0x0800 && ipOffset + 20 <= end) {
          const ihl = (bytes[ipOffset] & 15) * 4, proto = bytes[ipOffset + 9];
          if ((bytes[ipOffset] >> 4) === 4 && ihl >= 20 && ipOffset + ihl <= end) {
            const fragmentOffset = view.getUint16(ipOffset + 6) & 0x1fff;
            packet.src = `${bytes[ipOffset+12]}.${bytes[ipOffset+13]}.${bytes[ipOffset+14]}.${bytes[ipOffset+15]}`;
            packet.dst = `${bytes[ipOffset+16]}.${bytes[ipOffset+17]}.${bytes[ipOffset+18]}.${bytes[ipOffset+19]}`;
            packet.protocol = proto === 6 ? "TCP" : proto === 17 ? "UDP" : `IPv4 (${proto})`;
            if (fragmentOffset) packet.protocol += " (fragment)";
            if (!fragmentOffset && (proto === 6 || proto === 17) && ipOffset + ihl + 4 <= end) {
              const portOffset = ipOffset + ihl;
              packet.srcPort = view.getUint16(portOffset); packet.dstPort = view.getUint16(portOffset + 2);
              packet.ports = `${packet.srcPort} ${packet.dstPort}`;
              packet.src += `:${packet.srcPort}`; packet.dst += `:${packet.dstPort}`;
            }
          }
        } else if (etherType === 0x86dd) packet.protocol = "IPv6 (not decoded)";
      }
      parsed.push(packet); offset = end;
    }
    packets = parsed;
    let minLength = Infinity, maxLength = 0;
    for (const packet of parsed) { minLength = Math.min(minLength, packet.original); maxLength = Math.max(maxLength, packet.original); }
    $("#pcapStatus").textContent = `${parsed.length} packets · version ${major}.${minor} · link type Ethernet · captured ${formatBytes(bytes.length)} · packet lengths ${parsed.length ? minLength + "–" + maxLength + " bytes" : "n/a"}. PCAPNG unsupported.`;
    if (parsed.length) {
      const valid = parsed.filter(p => p.protocol === "TCP" || p.protocol === "UDP");
      const protocols = [...new Set(valid.map(p => p.protocol))].join(", ") || "No decoded TCP/UDP";
      const firstPacketTime = parsed[0].sec * 1000 + parsed[0].fraction / (parsed[0].fractionDivisor / 1000);
      timeline.push({ epoch: firstPacketTime, original: new Date(firstPacketTime).toISOString(), source: file.name, description: `${parsed.length} packets; decoded protocols: ${protocols}`, status: "PCAP timestamp (UTC)" });
      renderTimeline(); saveCaseData("Imported PCAP summary to timeline", file.name);
    }
    renderPackets();
  }).catch(error => { packets = []; renderPackets(); $("#pcapStatus").textContent = `Could not parse capture: ${error.message}`; });
}
function renderPackets() {
  const body = $("#packetRows"); body.replaceChildren();
  const filtered = getFilteredPackets();
  for (const p of filtered.slice(0, 5000)) {
    const timestamp = new Date(p.sec * 1000 + p.fraction / (p.fractionDivisor / 1000)).toISOString();
    const tr = el("tr"); tr.dataset.packet = p.number;
    [p.number, timestamp, p.protocol, p.src, p.dst, `${p.captured} / ${p.original}`].forEach(v => tr.append(el("td", v))); body.append(tr);
  }
  $("#packetRows").onclick = event => {
    const number = Number(event.target.closest("tr")?.dataset.packet);
    const packet = packets.find(item => item.number === number);
    if (packet) $("#packetDetail").textContent = `Packet ${packet.number}\nUTC: ${new Date(packet.sec * 1000 + packet.fraction / (packet.fractionDivisor / 1000)).toISOString()}\nProtocol: ${packet.protocol}\nSource: ${packet.src}\nDestination: ${packet.dst}\nCaptured/original length: ${packet.captured}/${packet.original}\nCapture byte offset: ${packet.offset}\nFirst captured bytes: ${packet.observedHex}`;
  };
}
function getFilteredPackets() {
  const filter = $("#packetFilter").value.trim().toLowerCase();
  const from = $("#packetFrom").valueAsNumber, to = $("#packetTo").valueAsNumber;
  return packets.filter(p => {
    const ms = p.sec * 1000 + p.fraction / (p.fractionDivisor / 1000);
    return `${p.protocol} ${p.src} ${p.dst}`.toLowerCase().includes(filter) && (!Number.isFinite(from) || ms >= from) && (!Number.isFinite(to) || ms <= to);
  });
}

function parseTimestamp(text, object) {
  const candidates = [object?.timestamp, object?.time, object?.date, object?.["@timestamp"]];
  const epoch = candidates.find(value => typeof value === "number");
  if (epoch !== undefined) {
    const ms = Math.abs(epoch) < 1e11 ? epoch * 1000 : epoch;
    const date = new Date(ms);
    return Number.isNaN(date.getTime()) ? null : { epoch: date.getTime(), original: String(epoch), status: "Parsed numeric epoch; seconds/ms inferred" };
  }
  const match = text.match(/\b(20\d\d[-/]\d\d?[-/]\d\d?(?:[T ]\d\d:\d\d:\d\d(?:\.\d+)?(?:Z|[+-]\d\d:?\d\d)?)?)/);
  if (!match) return null;
  const raw = match[1], hasZone = /(?:Z|[+-]\d\d:?\d\d)$/i.test(raw);
  if (!hasZone && !/^\d{4}-\d\d-\d\d$/.test(raw)) return { epoch: null, original: raw, status: "Ambiguous local time; not normalized" };
  const date = new Date(raw);
  return Number.isNaN(date.getTime()) ? null : { epoch: date.getTime(), original: raw, status: hasZone || /^\d{4}-\d\d-\d\d$/.test(raw) ? "Parsed with explicit/UTC date" : "Ambiguous" };
}
function severityOf(text) {
  if (/\b(panic|fatal|critical|crit|emergency|alert)\b/i.test(text)) return "critical";
  if (/\b(error|err|failed|failure|denied|invalid password)\b/i.test(text)) return "error";
  if (/\b(warn|warning|suspicious)\b/i.test(text)) return "warning";
  if (/\b(info|notice|accepted|session opened)\b/i.test(text)) return "info";
  return "unknown";
}
function parseLogs(file) {
  if (file.size > 12 * 1024 * 1024) { $("#logStatus").textContent = "Log is larger than the 12 MiB text-workbench limit."; return; }
  file.text().then(text => {
    const lines = text.split(/\r?\n/).slice(0, 50000);
    logs = lines.map((original, index) => {
      let object = null;
      if (/^\s*[{[]/.test(original)) { try { object = JSON.parse(original); } catch (_) { /* Keep malformed source line intact. */ } }
      const time = parseTimestamp(original, object);
      const source = object ? object.source || object.host || object.hostname || object.provider || "JSON record" : (original.match(/\b(?:sshd|sudo|kernel|systemd|auth|cron)\b/i) || [""])[0] || "Text log";
      const message = String(object ? (object.message ?? object.msg ?? original) : original);
      return { line: index + 1, original, time, severity: severityOf(original), source: String(source), message, potential: /failed password|invalid user|authentication failure|login failed/i.test(original) };
    }).filter(item => item.original.length);
    const failures = logs.filter(item => item.potential).length;
    $("#logStatus").textContent = `${logs.length} lines loaded · ${failures} potential authentication-failure keyword match(es) (heuristic, not a confirmed attack).`;
    renderLogs();
    const dated = logs.filter(row => row.time?.epoch !== null && row.time);
    timeline = timeline.concat(dated.slice(0, 2000).map(row => ({ epoch: row.time.epoch, original: row.time.original, source: `${file.name}:${row.line}`, description: row.message.slice(0, 500), status: row.time.status })));
    renderTimeline();
    if (dated.length) saveCaseData("Imported log timestamps to timeline", `${file.name}: ${Math.min(dated.length, 2000)} entries`);
  }).catch(error => { $("#logStatus").textContent = `Could not read log: ${error.message}`; });
}
function renderLogs() {
  const body = $("#logRows"); body.replaceChildren();
  for (const item of getFilteredLogs().slice(0, 3000)) {
    const tr = el("tr");
    [item.line, item.time?.original || item.time?.status || "No timestamp parsed", item.severity, item.source, item.original].forEach(value => tr.append(el("td", value)));
    if (item.potential) tr.classList.add("potential");
    body.append(tr);
  }
}
function getFilteredLogs() {
  const query = $("#logSearch").value.toLowerCase(), severity = $("#severityFilter").value;
  const from = $("#logFrom").valueAsNumber, to = $("#logTo").valueAsNumber;
  return logs.filter(row => {
    const matchesText = !query || `${row.original} ${row.source}`.toLowerCase().includes(query);
    const matchesSeverity = !severity || row.severity === severity;
    const time = row.time?.epoch;
    const matchesDate = (!Number.isFinite(from) && !Number.isFinite(to)) || (time !== null && time !== undefined && (!Number.isFinite(from) || time >= from) && (!Number.isFinite(to) || time <= to));
    return matchesText && matchesSeverity && matchesDate;
  });
}
function renderTimeline() {
  const body = $("#timelineRows"); body.replaceChildren();
  for (const item of timeline) {
    const tr = el("tr");
    [item.epoch === null ? "Uncertain" : new Date(item.epoch).toISOString(), item.original || "", item.source || "", item.description || "", item.status || "Manual observation"].forEach(value => tr.append(el("td", value)));
    body.append(tr);
  }
}

function parseClassicPcapExport() {
  const filtered = getFilteredPackets();
  download("tracelab-packets.csv", csv([["packet", "timestamp_utc", "protocol", "source", "destination", "captured_length", "original_length"], ...filtered.map(p => [p.number, new Date(p.sec * 1000 + p.fraction / (p.fractionDivisor / 1000)).toISOString(), p.protocol, p.src, p.dst, p.captured, p.original])]), "text/csv");
}

function buildOsintLinks() {
  const container = $("#osintLinks"); container.replaceChildren();
  const username = $("#osintUsername").value.trim();
  const domain = $("#osintDomain").value.trim().replace(/^https?:\/\//i, "").replace(/\/.*$/, "");
  const ip = $("#osintIp").value.trim();
  const links = [];
  if (username) {
    const q = encodeURIComponent(username);
    links.push(["GitHub users", `https://github.com/search?q=${q}&type=users`], ["Reddit search", `https://www.reddit.com/search/?q=${q}`], ["Mastodon directory/search", `https://mastodon.social/search?q=${q}`]);
  }
  if (domain) {
    const q = encodeURIComponent(domain);
    links.push(["ICANN RDAP lookup", `https://lookup.icann.org/en/lookup?name=${q}`], ["Certificate Transparency (crt.sh)", `https://crt.sh/?q=${q}`], ["DNS research (Google Public DNS)", `https://dns.google/resolve?name=${q}&type=ANY`]);
  }
  if (ip) {
    const q = encodeURIComponent(ip);
    links.push(["RDAP / registration lookup", `https://rdap.org/ip/${q}`], ["AbuseIPDB public check", `https://www.abuseipdb.com/check/${q}`], ["VirusTotal public IP page", `https://www.virustotal.com/gui/ip-address/${q}`]);
  }
  for (const [label, href] of links) {
    const a = el("a", label); a.href = href; a.target = "_blank"; a.rel = "noopener noreferrer"; a.addEventListener("click", () => saveCaseData("Opened external OSINT link", label));
    container.append(a);
  }
  if (!links.length) container.append(el("p", "Enter a public username, domain, or IP to generate links.", "status"));
  else notify("Links generated only. No identifier was sent until you open a link.");
}

function renderOsintNotes() {
  const list = $("#osintNotes"); list.replaceChildren();
  for (const item of osintNotes) {
    const li = el("li", `${item.time} · ${item.url} · ${item.note}`);
    list.append(li);
  }
}

function wireEvents() {
  $$(".nav-button").forEach(button => button.addEventListener("click", () => {
    $$(".nav-button").forEach(item => item.classList.toggle("active", item === button));
    $$(".tab-view").forEach(view => view.classList.toggle("active", view.id === `tab-${button.dataset.tab}`));
  }));
  $("#chooseFile").addEventListener("click", () => $("#fileInput").click());
  $("#fileInput").addEventListener("change", event => { if (event.target.files[0]) inspectFile(event.target.files[0]); });
  $("#clearFile").addEventListener("click", clearFile);
  const dropzone = $("#dropzone");
  dropzone.addEventListener("dragover", event => { event.preventDefault(); dropzone.classList.add("dragging"); });
  dropzone.addEventListener("dragleave", () => dropzone.classList.remove("dragging"));
  dropzone.addEventListener("drop", event => { event.preventDefault(); dropzone.classList.remove("dragging"); if (event.dataTransfer.files[0]) inspectFile(event.dataTransfer.files[0]); });
  $("#hashCards").addEventListener("click", async event => {
    const button = event.target.closest("button"); if (!button) return;
    const card = button.closest(".hash-card"), value = card?.dataset.full;
    if (!value) { notify("Hash is not available."); return; }
    if (button.classList.contains("reveal")) {
      const show = button.textContent === "Show full";
      card.querySelector(".hash-value").textContent = show ? value : shortHash(value);
      button.textContent = show ? "Show partial" : "Show full";
    } else if (button.classList.contains("copy")) {
      try { await navigator.clipboard.writeText(value); notify(`${card.dataset.alg} copied.`); }
      catch (error) { notify(`Clipboard unavailable: ${error.message}`); }
    }
  });
  $("#offsetInput").addEventListener("change", renderHex);
  $("#prevBytes").addEventListener("click", () => { $("#offsetInput").value = Math.max(0, Number($("#offsetInput").value) - 256); renderHex(); });
  $("#nextBytes").addEventListener("click", () => { $("#offsetInput").value = Number($("#offsetInput").value) + 256; renderHex(); });
  $("#exportReport").addEventListener("click", () => {
    if (!primaryRecord) { notify("Select a file with successful analysis first."); return; }
    saveCaseData("Generated file report", primaryRecord.name);
    download("tracelab-file-report.json", JSON.stringify({ tool: "TraceLab", version: "2.0", generatedAt: new Date().toISOString(), processing: "Browser local only", file: primaryRecord, limitations: "Browser metadata only; signature is indicative, not proof of complete format or safety." }, null, 2));
  });
  $("#compareButton").addEventListener("click", compareFiles);
  $("#pcapInput").addEventListener("change", event => { if (event.target.files[0]) $("#pcapStatus").textContent = `Selected ${event.target.files[0].name}. Click Inspect capture.`; });
  $("#parsePcap").addEventListener("click", () => { if ($("#pcapInput").files[0]) parsePcap($("#pcapInput").files[0]); else $("#pcapStatus").textContent = "Choose a PCAP file first."; });
  $("#packetFilter").addEventListener("input", renderPackets);
  $("#packetFrom").addEventListener("change", renderPackets); $("#packetTo").addEventListener("change", renderPackets);
  $("#exportPackets").addEventListener("click", parseClassicPcapExport);
  $("#logInput").addEventListener("change", event => { if (event.target.files[0]) parseLogs(event.target.files[0]); });
  $("#logSearch").addEventListener("input", renderLogs); $("#severityFilter").addEventListener("change", renderLogs);
  $("#logFrom").addEventListener("change", renderLogs); $("#logTo").addEventListener("change", renderLogs);
  $("#exportLogs").addEventListener("click", () => {
    const rows = getFilteredLogs();
    download("tracelab-filtered-logs.csv", csv([["line", "timestamp_original", "timestamp_status", "severity", "source", "potential_indicator", "original"], ...rows.map(r => [r.line, r.time?.original || "", r.time?.status || "unparsed", r.severity, r.source, r.potential, r.original])]), "text/csv");
  });
  $("#addNote").addEventListener("click", () => {
    const description = $("#noteDescription").value.trim();
    if (!description) { notify("Enter an observation first."); return; }
    const raw = $("#noteTime").value;
    const date = raw ? new Date(raw) : null;
    timeline.push({ epoch: date && !Number.isNaN(date.getTime()) ? date.getTime() : null, original: raw || "No time supplied", source: $("#noteSource").value.trim() || "Investigator note", description, status: raw ? "Manual time (interpreted from local input)" : "Time not supplied" });
    $("#noteDescription").value = ""; renderTimeline(); saveCaseData("Added timeline note", description);
  });
  $("#addFileTimeline").addEventListener("click", () => {
    if (!primaryRecord) { notify("Analyze a file first."); return; }
    const hasTime = Number.isFinite(primaryRecord.lastModified) && primaryRecord.lastModified > 0;
    timeline.push({
      epoch: hasTime ? primaryRecord.lastModified : null,
      original: hasTime ? new Date(primaryRecord.lastModified).toISOString() : "No modification timestamp supplied",
      source: primaryRecord.name,
      description: "Browser-reported file last-modified timestamp; not necessarily capture or acquisition time.",
      status: hasTime ? "Browser file property; not verified event time" : "Timestamp unavailable"
    });
    renderTimeline(); saveCaseData("Added file timestamp to timeline", primaryRecord.name);
  });
  $("#timelineSort").addEventListener("click", () => { timeline.sort((a,b) => (a.epoch ?? Infinity) - (b.epoch ?? Infinity)); renderTimeline(); });
  $("#exportTimeline").addEventListener("click", () => {
    saveCaseData("Exported timeline CSV", `${timeline.length} event(s)`);
    download("tracelab-timeline.csv", csv([["time_utc", "original_time", "source", "description", "status"], ...timeline.map(e => [e.epoch === null ? "" : new Date(e.epoch).toISOString(), e.original, e.source, e.description, e.status])]), "text/csv");
  });
  $("#saveCase").addEventListener("click", () => { caseData.caseId = $("#caseId").value.trim(); caseData.title = $("#caseTitle").value.trim(); caseData.notes = $("#caseNotes").value; saveCaseData("Saved case details", caseData.caseId); notify("Case details saved locally."); });
  $("#addEvidence").addEventListener("click", () => {
    if (!primaryRecord) { notify("Analyze a file successfully first."); return; }
    const id = `E-${String(caseData.evidence.length + 1).padStart(4, "0")}`;
    caseData.evidence.push({ id, name: primaryRecord.name, size: primaryRecord.size, type: primaryRecord.signature.label, mime: primaryRecord.mime, sha256: primaryRecord.hashes["SHA-256"], md5: primaryRecord.hashes.MD5, addedAt: new Date().toISOString(), analysisAt: new Date().toISOString() });
    saveCaseData("Added evidence item", `${id}: ${primaryRecord.name}`); notify("Evidence metadata added; file bytes were not stored.");
  });
  $("#exportCase").addEventListener("click", () => {
    caseData.caseId = $("#caseId").value.trim(); caseData.title = $("#caseTitle").value.trim(); caseData.notes = $("#caseNotes").value;
    saveCaseData("Generated case report", caseData.caseId);
    download("tracelab-case.json", JSON.stringify({ ...caseData, generatedAt: new Date().toISOString(), tool: "TraceLab 2.0", auditLogTamperProof: false, chainOfCustodyNote: "Requires independently controlled procedures." }, null, 2));
  });
  $("#exportInventory").addEventListener("click", () => {
    saveCaseData("Exported evidence inventory CSV", `${caseData.evidence.length} item(s)`);
    download("tracelab-evidence-inventory.csv", csv([["evidence_id","filename","size_bytes","type","mime","sha256","md5","added_at"], ...caseData.evidence.map(e => [e.id,e.name,e.size,e.type,e.mime,e.sha256,e.md5,e.addedAt])]), "text/csv");
  });
  $("#importCase").addEventListener("change", async event => {
    const file = event.target.files[0]; if (!file) return;
    try {
      if (file.size > 2 * 1024 * 1024) throw new Error("JSON file exceeds 2 MiB.");
      const value = JSON.parse(await file.text());
      if (value.schemaVersion !== 2 || typeof value.caseId !== "string" || typeof value.title !== "string" || typeof value.notes !== "string" || !Array.isArray(value.evidence) || !Array.isArray(value.audit)) throw new Error("Unsupported or invalid TraceLab case schema.");
      if (!value.evidence.every(e => e && typeof e.id === "string" && typeof e.name === "string" && Number.isFinite(e.size))) throw new Error("Evidence item validation failed.");
      if (!value.audit.every(item => item && typeof item.time === "string" && typeof item.action === "string" && typeof item.details === "string")) throw new Error("Audit log validation failed.");
      if (value.timeline !== undefined && (!Array.isArray(value.timeline) || !value.timeline.every(item => item && typeof item.description === "string" && (item.epoch === null || Number.isFinite(item.epoch) && Math.abs(item.epoch) <= 8640000000000000)))) throw new Error("Timeline validation failed.");
      caseData = { schemaVersion: 2, caseId: value.caseId, title: value.title, notes: value.notes, evidence: value.evidence, audit: value.audit.slice(0, 500), timeline: value.timeline || [] };
      timeline = caseData.timeline;
      saveCaseData("Imported case JSON", file.name); renderCase(); renderTimeline(); notify("Case JSON imported and validated.");
    } catch (error) { $("#storageStatus").textContent = `Import failed: ${error.message}`; notify("Case import failed."); }
    event.target.value = "";
  });
  $("#clearCase").addEventListener("click", () => {
    if (!confirm("Clear the locally stored case, evidence inventory and audit log? This cannot be undone.")) return;
    try { localStorage.removeItem(CASE_KEY); caseData = { schemaVersion: 2, caseId: "", title: "", notes: "", evidence: [], audit: [], timeline: [] }; timeline = []; renderTimeline(); renderCase(); notify("Stored case cleared."); }
    catch (error) { $("#storageStatus").textContent = `Could not clear stored case: ${error.message}`; }
  });
  $("#buildOsint").addEventListener("click", buildOsintLinks);
  $("#addOsintNote").addEventListener("click", () => {
    const url = $("#osintUrl").value.trim(), note = $("#osintObservation").value.trim();
    if (!url || !note) { notify("Enter both a public source URL and observation."); return; }
    try { const parsed = new URL(url); if (!["https:", "http:"].includes(parsed.protocol)) throw new Error("Only HTTP(S) URLs allowed."); }
    catch (_) { notify("Enter a valid HTTP(S) source URL."); return; }
    osintNotes.unshift({ time: new Date().toISOString(), url, note }); renderOsintNotes();
    $("#osintUrl").value = ""; $("#osintObservation").value = "";
  });
  $("#exportOsint").addEventListener("click", () => download("tracelab-public-research-notes.json", JSON.stringify(osintNotes, null, 2)));
  $("#textHashButton").addEventListener("click", async () => {
    try { $("#textHashOutput").textContent = hex(new Uint8Array(await crypto.subtle.digest("SHA-256", new TextEncoder().encode($("#textHashInput").value)))); }
    catch (error) { $("#textHashOutput").textContent = `SHA-256 unavailable: ${error.message}`; }
  });
  $("#encodeButton").addEventListener("click", () => { const bytes = new TextEncoder().encode($("#base64Input").value); let binary = ""; bytes.forEach(byte => binary += String.fromCharCode(byte)); $("#base64Output").textContent = btoa(binary); });
  $("#decodeButton").addEventListener("click", () => {
    try { const binary = atob($("#base64Input").value.trim()); $("#base64Output").textContent = new TextDecoder("utf-8", { fatal: true }).decode(Uint8Array.from(binary, c => c.charCodeAt(0))); }
    catch (error) { $("#base64Output").textContent = `Invalid Base64 or invalid UTF-8: ${error.message}`; }
  });
  $("#toHex").addEventListener("click", () => { $("#hexTextOutput").textContent = hex(new TextEncoder().encode($("#hexTextInput").value)).match(/.{1,2}/g)?.join(" ") || ""; });
  $("#fromHex").addEventListener("click", () => {
    try {
      const cleaned = $("#hexTextInput").value.replace(/\s+/g, "");
      if (!/^(?:[0-9a-fA-F]{2})*$/.test(cleaned)) throw new Error("Enter complete pairs of hexadecimal digits.");
      $("#hexTextOutput").textContent = new TextDecoder("utf-8", { fatal: true }).decode(Uint8Array.from(cleaned.match(/../g) || [], pair => parseInt(pair, 16)));
    } catch (error) { $("#hexTextOutput").textContent = `Invalid hex/UTF-8: ${error.message}`; }
  });
  $("#checkUtf8").addEventListener("click", () => {
    try { const cleaned = $("#hexTextInput").value.replace(/\s+/g, ""); if (!/^(?:[0-9a-fA-F]{2})*$/.test(cleaned)) throw new Error("Invalid hex bytes."); new TextDecoder("utf-8", { fatal: true }).decode(Uint8Array.from(cleaned.match(/../g) || [], pair => parseInt(pair, 16))); $("#hexTextOutput").textContent = "Valid UTF-8 byte sequence."; }
    catch (error) { $("#hexTextOutput").textContent = `Invalid UTF-8: ${error.message}`; }
  });
  $("#urlEncode").addEventListener("click", () => { $("#formatOutput").textContent = encodeURIComponent($("#formatInput").value); });
  $("#urlDecode").addEventListener("click", () => { try { $("#formatOutput").textContent = decodeURIComponent($("#formatInput").value); } catch (error) { $("#formatOutput").textContent = `Invalid URL encoding: ${error.message}`; } });
  $("#formatJson").addEventListener("click", () => { try { $("#formatOutput").textContent = JSON.stringify(JSON.parse($("#formatInput").value), null, 2); } catch (error) { $("#formatOutput").textContent = `Invalid JSON: ${error.message}`; } });
  $("#rot13").addEventListener("click", () => { $("#formatOutput").textContent = $("#formatInput").value.replace(/[a-zA-Z]/g, c => String.fromCharCode(c.charCodeAt(0) + (c.toLowerCase() <= "m" ? 13 : -13))); });
  $("#timestampButton").addEventListener("click", () => {
    const value = Number($("#timestampInput").value.trim());
    if (!Number.isFinite(value)) { $("#timestampOutput").textContent = "Enter a numeric Unix timestamp."; return; }
    const date = new Date(Math.abs(value) < 1e11 ? value * 1000 : value);
    $("#timestampOutput").textContent = Number.isNaN(date.getTime()) ? "Timestamp is outside the supported date range." : `${date.toLocaleString()} · ${date.toISOString()}`;
  });
}

document.addEventListener("DOMContentLoaded", () => {
  timeline = Array.isArray(caseData.timeline) ? caseData.timeline : [];
  wireEvents();
  renderCase(); renderTimeline(); renderOsintNotes(); renderHex();
});
