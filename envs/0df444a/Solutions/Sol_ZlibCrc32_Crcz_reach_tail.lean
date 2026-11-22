-- Prove2me | solution 1 for ZlibCrc32.Crcz.reach_tail
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T13:26:01.572887+00:00
-- url     : https://prove2.me/submissions/32dac1d5-7084-420b-ab28-72daf00464a3

import Mathlib.Tactic.IntervalCases
import Definitions.Def_ZlibCrc32_CrczModel
import Mathlib.Data.List.GetD

section
/-! # Instruction fetch for the placed `zlibCrc32` text block (adapted from the byte-table pilot) -/

namespace ZlibCrc32.Crcz

set_option maxRecDepth 100000

open Arm64 Arm64.Obj


theorem length_bytesOfWordLE (w : BitVec 32) : (bytesOfWordLE w).length = 4 := by
  simp [bytesOfWordLE, bytesLE]

theorem drop_take_flatMap_bytesOfWordLE {α : Type} (g : α → BitVec 32) :
    ∀ (L : List α) (j : Nat) (hj : j < L.length),
      ((L.flatMap fun a => bytesOfWordLE (g a)).drop (4 * j)).take 4 =
        bytesOfWordLE (g (L[j]'hj))
  | [], _, hj => by simp at hj
  | a :: L, 0, _ => by
    simp only [List.flatMap_cons, Nat.mul_zero, List.drop_zero, List.getElem_cons_zero]
    rw [List.take_append_of_le_length (by simp [length_bytesOfWordLE])]
    exact List.take_of_length_le (by simp [length_bytesOfWordLE])
  | a :: L, j + 1, hj => by
    simp only [List.flatMap_cons, List.getElem_cons_succ]
    rw [show 4 * (j + 1) = (bytesOfWordLE (g a)).length + 4 * j by
          simp [length_bytesOfWordLE]; omega,
      ← List.drop_drop, List.drop_left]
    exact drop_take_flatMap_bytesOfWordLE g L j (by simp at hj; omega)

theorem take4_drop_patched {blk : CodeBlock} {pl : Placement} {off : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ blk.code.length) :
    ((blk.patched pl).drop off).take 4 = bytesOfWordLE (blk.patchedWord pl off) := by
  have hj : off / 4 < (List.range (blk.code.length / 4)).length := by
    simp only [List.length_range]; omega
  have h := drop_take_flatMap_bytesOfWordLE (fun j => blk.patchedWord pl (4 * j))
    (List.range (blk.code.length / 4)) (off / 4) hj
  rw [List.getElem_range, show 4 * (off / 4) = off by omega] at h
  exact h

theorem codeLoaded_cell {p : Program} {m : Memory} (h : p.CodeLoaded m) (i : Nat)
    (hi : i < p.code.length) :
    m.read8 (p.base + BitVec.ofNat 64 i) = p.code[i] ∧
    m.perm (p.base + BitVec.ofNat 64 i) = some Perm.rx := by
  unfold Program.CodeLoaded at h
  exact ⟨(h.2.2 i hi).1, (h.2.2 i hi).2.1⟩

set_option maxRecDepth 100000 in
theorem code_length : zlibCrc32PlacedCode.length = 2824 := by rfl

theorem patched_length (pl : Placement) : (zlibCrc32Text.patched pl).length = 2824 := by
  unfold CodeBlock.patched
  rw [List.length_flatMap]
  simp only [length_bytesOfWordLE]
  show (List.map (fun _ => 4) (List.range (zlibCrc32PlacedCode.length / 4))).sum = 2824
  rw [code_length]; rfl

theorem hook_none (pl : Placement) (pc : BitVec 64) : (prog pl).externAt? pc = none := by
  simp [prog, Program.externAt?, Program.hookAtOff?, PlacedLib.program, zlibCrc32Lib, zlibCrc32Text]

theorem read8_code {pl : Placement} {m : Memory} (hCL : (prog pl).CodeLoaded m) {off k : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 2824) (hk : k < 4) :
    m.read8 (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      (zlibCrc32Text.patchedWord pl off).extractLsb' (8 * k) 8 ∧
    m.perm (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) = some Perm.rx := by
  have hl : (prog pl).code.length = 2824 := patched_length pl
  have h := codeLoaded_cell hCL (off + k) (by omega)
  have ha : pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k =
      (prog pl).base + BitVec.ofNat 64 (off + k) := by
    show _ = pl.base + _
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [ha]
  refine ⟨?_, h.2⟩
  rw [h.1]
  have ht := take4_drop_patched (blk := zlibCrc32Text) (pl := pl) hal
    (by rw [show zlibCrc32Text.code = zlibCrc32PlacedCode from rfl, code_length]; exact hlen)
  have e1 : (prog pl).code[off + k]'(by omega) =
      (((zlibCrc32Text.patched pl).drop off).take 4)[k]'(by
        simp [List.length_take, List.length_drop, patched_length]; omega) := by
    simp only [List.getElem_take, List.getElem_drop]; rfl
  rw [e1]
  simp only [ht, bytesOfWordLE, bytesLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  have : 8 * k + i < 32 := by omega
  simp [hi, this]; omega

theorem fetch_word {pl : Placement} {m : Memory} (hP : zlibCrc32Lib.Placeable pl)
    (hCL : (prog pl).CodeLoaded m) {off : Nat} (hal : off % 4 = 0) (hlen : off + 4 ≤ 2824) :
    (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      decode (zlibCrc32Text.patchedWord pl off) := by
  have hb4 : pl.base.toNat % 4 = 0 := by
    have := hP.text.base_aligned; simpa [zlibCrc32Lib, zlibCrc32Text] using this
  have hnw : pl.base.toNat + 2824 ≤ 2 ^ 64 := by
    have := hP.text.no_wrap
    have hl : zlibCrc32Text.code.length = 2824 := code_length
    rw [show zlibCrc32Lib.text = zlibCrc32Text from rfl, hl] at this
    exact this
  have hpc : (pl.base + BitVec.ofNat 64 off).toNat % 4 = 0 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    have h1 : off % 2 ^ 64 = off := Nat.mod_eq_of_lt (by omega)
    have h2 : (pl.base.toNat + off) % 2 ^ 64 = pl.base.toNat + off := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2]; omega
  have r0 := read8_code hCL hal hlen (k := 0) (by omega)
  have r1 := read8_code hCL hal hlen (k := 1) (by omega)
  have r2 := read8_code hCL hal hlen (k := 2) (by omega)
  have r3 := read8_code hCL hal hlen (k := 3) (by omega)
  simp only [Program.fetchMem, hook_none, Option.isSome_none, Bool.false_eq_true, if_false, hpc,
    ne_eq, not_true_eq_false]
  generalize ha : pl.base + BitVec.ofNat 64 off = a at *
  simp only [Nat.mul_zero, Nat.mul_one, Nat.reduceMul] at r0 r1 r2 r3
  have hx : m.canExec a 4 = true := by
    simp only [Memory.canExec, Memory.allPerm, BitVec.add_assoc, BitVec.reduceAdd]
    simp only [BitVec.add_zero] at r0
    simp [r0.2, r1.2, r2.2, r3.2, Perm.rx]
  simp only [hx, Bool.not_true, Bool.false_eq_true, if_false]
  congr 1
  simp only [Memory.read32]
  rw [r0.1, r1.1, r2.1, r3.1]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

theorem patchedWord_plain (pl : Placement) {off : Nat} (h : zlibCrc32Text.relocAt? off = none) :
    zlibCrc32Text.patchedWord pl off = zlibCrc32Text.wordAt off := by
  simp [CodeBlock.patchedWord, h]

/-- Fetch of a plain (unrelocated) word, decoded by `rfl`. -/
theorem fetch_plain {pl : Placement} {m : Memory} (hP : zlibCrc32Lib.Placeable pl)
    (hCL : (prog pl).CodeLoaded m) (off : Nat) (hal : off % 4 = 0) (hlen : off + 4 ≤ 2824)
    (hr : zlibCrc32Text.relocAt? off = none) :
    (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 off) = decode (zlibCrc32Text.wordAt off) := by
  rw [fetch_word hP hCL hal hlen, patchedWord_plain pl hr]

end ZlibCrc32.Crcz
end

section
/-! # The instructions of `crc32_z` (generated by gen_code5.py)

The 508 words of `crc32_z` (padded to 512) are checked once against the object's bytes, in 16
chunks of 32 words, so that each per-address fetch lemma decodes one word found in a short list. -/

namespace ZlibCrc32.Crcz

open Arm64 Arm64.Obj

/-- Four-byte little-endian words of a byte list, `n` of them. -/
def wordsOf : List (BitVec 8) → Nat → List (BitVec 32)
  | a :: b :: c :: d :: rest, n + 1 => wordOfBytesLE [a, b, c, d] 0 :: wordsOf rest n
  | _, _ => []

theorem wordOfBytesLE_cons (a : BitVec 8) (l : List (BitVec 8)) (i : Nat) :
    wordOfBytesLE (a :: l) (i + 1) = wordOfBytesLE l i := by
  simp [wordOfBytesLE, Nat.add_assoc, Nat.add_comm 1]

theorem wordOfBytesLE_drop (l : List (BitVec 8)) (d i : Nat) :
    wordOfBytesLE l (d + i) = wordOfBytesLE (l.drop d) i := by
  induction d generalizing l with
  | zero => simp
  | succ d ih =>
    cases l with
    | nil => simp [wordOfBytesLE]
    | cons a l => rw [show d + 1 + i = (d + i) + 1 by omega, wordOfBytesLE_cons, ih]; rfl

theorem wordOfBytesLE_four (a b c d : BitVec 8) (l : List (BitVec 8)) :
    wordOfBytesLE (a :: b :: c :: d :: l) 0 = wordOfBytesLE [a, b, c, d] 0 := by
  simp [wordOfBytesLE]

theorem wordsOf_getD : ∀ (n : Nat) (l : List (BitVec 8)) (k : Nat), k < n → 4 * n ≤ l.length →
    wordOfBytesLE l (4 * k) = (wordsOf l n).getD k 0#32
  | 0, _, _, hk, _ => absurd hk (by omega)
  | n + 1, a :: b :: c :: d :: l, k, hk, hl => by
    cases k with
    | zero => simp [wordsOf, wordOfBytesLE_four]
    | succ k =>
      simp only [wordsOf, List.getD_cons_succ]
      rw [show 4 * (k + 1) = 4 + 4 * k by omega, wordOfBytesLE_drop]
      exact wordsOf_getD n l k (by omega) (by simp at hl; omega)
  | n + 1, [], _, _, hl => by simp at hl
  | n + 1, [_], _, _, hl => by simp at hl; omega
  | n + 1, [_, _], _, _, hl => by simp at hl; omega
  | n + 1, [_, _, _], _, _, hl => by simp at hl; omega

def cw0 : List (BitVec 32) := [0xb4000201#32, 0xf81a0ffe#32, 0xf100bc5f#32, 0x2a2003e9#32, 0x9000000d#32, 0x910001ad#32, 0xa9016ffc#32, 0xa90267fa#32, 0xa9035ff8#32, 0xa90457f6#32, 0xa9054ff4#32, 0x540000e2#32, 0xf100205f#32, 0x54003122#32, 0xb50036e2#32, 0x140001e5#32, 0xaa1f03e0#32, 0xd65f03c0#32, 0xf240083f#32, 0x54000a80#32, 0xaa0103ea#32, 0x3840154b#32, 0x4a09016b#32, 0x92401d6b#32, 0xb86b79ac#32, 0xf100044b#32, 0xca492189#32, 0x540008e0#32, 0x9240094c#32, 0xb40008ac#32, 0x3940042a#32, 0x4a09014a#32]

def cw1 : List (BitVec 32) := [0x92401d4a#32, 0xb86a79ab#32, 0xf100084a#32, 0xca492169#32, 0x9100082b#32, 0x54000800#32, 0x9240096c#32, 0xb40007cc#32, 0x3940082a#32, 0x4a09014a#32, 0x92401d4a#32, 0xb86a79ab#32, 0xf1000c4a#32, 0xca492169#32, 0x91000c2b#32, 0x540006c0#32, 0x9240096c#32, 0xb400068c#32, 0x39400c2a#32, 0x4a09014a#32, 0x92401d4a#32, 0xb86a79ab#32, 0xf100104a#32, 0xca492169#32, 0x9100102b#32, 0x54000580#32, 0x9240096c#32, 0xb400054c#32, 0x3940102a#32, 0x4a09014a#32, 0x92401d4a#32, 0xb86a79ab#32]

def cw2 : List (BitVec 32) := [0xf100144a#32, 0xca492169#32, 0x9100142b#32, 0x54000440#32, 0x9240096c#32, 0xb400040c#32, 0x3940142a#32, 0x4a09014a#32, 0x92401d4a#32, 0xb86a79ab#32, 0xf100184a#32, 0xca492169#32, 0x9100182b#32, 0x54000300#32, 0x9240096c#32, 0xb40002cc#32, 0x3940182a#32, 0x4a09014a#32, 0x92401d4a#32, 0xb86a79ab#32, 0xf1001c4a#32, 0xca492169#32, 0x91001c2b#32, 0x540001c0#32, 0x9240096c#32, 0xb400018c#32, 0x39401c2a#32, 0x91002021#32, 0xd1002042#32, 0x4a09014a#32, 0x92401d4a#32, 0xb86a79aa#32]

def cw3 : List (BitVec 32) := [0xca492149#32, 0x14000006#32, 0xaa0b03e2#32, 0xaa0a03e1#32, 0x14000003#32, 0xaa0a03e2#32, 0xaa0b03e1#32, 0xb202e7ea#32, 0x928004eb#32, 0xf29999aa#32, 0x9bca7c4a#32, 0xd345fd48#32, 0x9b0b0902#32, 0xf100050b#32, 0x54001300#32, 0x9000000c#32, 0x9100018c#32, 0x5282800d#32, 0x5283000f#32, 0x52838010#32, 0xaa1f03ee#32, 0xaa1f03f2#32, 0xaa1f03f3#32, 0xaa1f03e0#32, 0x8b0d018d#32, 0x8b0f018f#32, 0x8b100190#32, 0xaa0103f1#32, 0xf90007e8#32, 0xa9411225#32, 0x91100199#32, 0xa9401a27#32]

def cw4 : List (BitVec 32) := [0x91300188#32, 0xf9401223#32, 0xf100056b#32, 0x9100a231#32, 0xca0000b6#32, 0xca120095#32, 0xca0900f8#32, 0xca1300d7#32, 0x92401ec0#32, 0xb8607993#32, 0xd3483f00#32, 0xd3483efa#32, 0xca0e0069#32, 0x92401f0e#32, 0x92401ef2#32, 0xb86e798e#32, 0xb8727992#32, 0xb8607b20#32, 0xb87a7b3a#32, 0xd3483edc#32, 0xd3483ebe#32, 0xd3483d2a#32, 0x92401eb4#32, 0x92401d3b#32, 0xb8747994#32, 0xb87b799b#32, 0x4a0e000e#32, 0x4a120340#32, 0xb87c7b32#32, 0xb87e7b3a#32, 0xb86a7b2a#32, 0xd3505f19#32]

def cw5 : List (BitVec 32) := [0xd3505efc#32, 0x53187f18#32, 0x53187ef7#32, 0x4a130253#32, 0x4a140354#32, 0x9120019a#32, 0x4a1b0152#32, 0xd3505edb#32, 0x53187ed6#32, 0xb8797b4a#32, 0xb87c7b59#32, 0xd3505ebc#32, 0xb8787918#32, 0xb8777917#32, 0x53187eb5#32, 0xb87b7b5b#32, 0xb8767916#32, 0xb87c7b5c#32, 0xca0a030a#32, 0xca1902f7#32, 0xd3609cf8#32, 0xd3609cd9#32, 0xb8757915#32, 0xca1b02d6#32, 0x9140059b#32, 0xd3505d3e#32, 0x53187d29#32, 0xb8787b78#32, 0xb8797b79#32, 0xca1c02b5#32, 0xd3609cbc#32, 0xb87e7b5a#32]

def cw6 : List (BitVec 32) := [0xd3609c9e#32, 0xb8697908#32, 0xca0a0309#32, 0xca17032a#32, 0xb87c7b77#32, 0xd3609c79#32, 0xb87e7b78#32, 0xca000140#32, 0xca1602ea#32, 0xca1a0108#32, 0xca0e0129#32, 0xb8797b76#32, 0xca15030e#32, 0xca130155#32, 0xd368bcea#32, 0xd368bcd3#32, 0xca1401ce#32, 0xca0802c8#32, 0xd368bcb6#32, 0xd370dcb9#32, 0xca120114#32, 0xb86a79a8#32, 0xd370dcea#32, 0xb87379b2#32, 0xb87679b3#32, 0xd370dcd6#32, 0xb86a79ea#32, 0xd368bc97#32, 0xd368bc78#32, 0xb87679f6#32, 0xd370dc9a#32, 0xd378fce7#32]

def cw7 : List (BitVec 32) := [0xca080148#32, 0xd378fcc6#32, 0xd378fca5#32, 0xca1202ca#32, 0xb87979f2#32, 0xd370dc79#32, 0xd378fc84#32, 0xd378fc63#32, 0xb87779b7#32, 0xb87879b8#32, 0xb87a79f6#32, 0xca130252#32, 0xb87979f3#32, 0xb8677a07#32, 0xb8667a06#32, 0xb8657a05#32, 0xb8647a04#32, 0xb8637a03#32, 0xca1702d6#32, 0xca180277#32, 0xca0800e8#32, 0xca0a00ca#32, 0xca1200b2#32, 0xca090109#32, 0xca000153#32, 0xca160088#32, 0xca17006a#32, 0xca150240#32, 0xca0e0112#32, 0xca14014e#32, 0x54ffefe1#32, 0xf94007ea#32]

def cw8 : List (BitVec 32) := [0x52800508#32, 0x9000000d#32, 0x910001ad#32, 0x9b080548#32, 0xd100a101#32, 0x14000005#32, 0xaa1f03e0#32, 0xaa1f03f3#32, 0xaa1f03f2#32, 0xaa1f03ee#32, 0xa9402828#32, 0xca090108#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32]

def cw9 : List (BitVec 32) := [0xca482128#32, 0x92401d09#32, 0xd348fd08#32, 0xb86979a9#32, 0x4a080128#32, 0xca130149#32, 0xca080128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xd348fd08#32, 0xb86979a9#32, 0x4a080128#32]

def cw10 : List (BitVec 32) := [0xa941242a#32, 0xca00014a#32, 0xca120129#32, 0xca080148#32, 0x92401d0a#32, 0xb86a79aa#32, 0xca482148#32, 0x92401d0a#32, 0xb86a79aa#32, 0xca482148#32, 0x92401d0a#32, 0xb86a79aa#32, 0xca482148#32, 0x92401d0a#32, 0xb86a79aa#32, 0xca482148#32, 0x92401d0a#32, 0xb86a79aa#32, 0xca482148#32, 0x92401d0a#32, 0xb86a79aa#32, 0xca482148#32, 0x92401d0a#32, 0xb86a79aa#32, 0xca482148#32, 0x92401d0a#32, 0xd348fd08#32, 0xb86a79aa#32, 0x4a080148#32, 0xf940102a#32, 0x9100a021#32, 0xca080128#32]

def cw11 : List (BitVec 32) := [0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xd348fd08#32, 0xb86979a9#32, 0x4a080128#32, 0xca0e0149#32, 0xca080128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32]

def cw12 : List (BitVec 32) := [0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xb86979a9#32, 0xca482128#32, 0x92401d09#32, 0xd348fd08#32, 0xb86979a9#32, 0x4a080129#32, 0xf100205f#32, 0x54ffcf23#32, 0x39400028#32, 0xd1002042#32, 0x9100202a#32, 0xf1001c5f#32, 0x4a090108#32, 0x92401d08#32, 0xb86879a8#32, 0xca492108#32, 0x39400429#32, 0x4a080129#32]

def cw13 : List (BitVec 32) := [0x92401d29#32, 0xb86979a9#32, 0xca482128#32, 0x39400829#32, 0x4a080129#32, 0x92401d29#32, 0xb86979a9#32, 0xca482128#32, 0x39400c29#32, 0x4a080129#32, 0x92401d29#32, 0xb86979a9#32, 0xca482128#32, 0x39401029#32, 0x4a080129#32, 0x92401d29#32, 0xb86979a9#32, 0xca482128#32, 0x39401429#32, 0x4a080129#32, 0x92401d29#32, 0xb86979a9#32, 0xca482128#32, 0x39401829#32, 0x4a080129#32, 0x92401d29#32, 0xb86979a9#32, 0xca482128#32, 0x39401c29#32, 0xaa0a03e1#32, 0x4a080129#32, 0x92401d29#32]

def cw14 : List (BitVec 32) := [0xb86979a9#32, 0xca482129#32, 0x54fffa88#32, 0xaa0a03e1#32, 0xb4000602#32, 0x39400028#32, 0xf100045f#32, 0x4a090108#32, 0x92401d08#32, 0xb86879a8#32, 0xca492109#32, 0x54000520#32, 0x39400428#32, 0xf100085f#32, 0x4a090108#32, 0x92401d08#32, 0xb86879a8#32, 0xca492109#32, 0x54000440#32, 0x39400828#32, 0xf1000c5f#32, 0x4a090108#32, 0x92401d08#32, 0xb86879a8#32, 0xca492109#32, 0x54000360#32, 0x39400c28#32, 0xf100105f#32, 0x4a090108#32, 0x92401d08#32, 0xb86879a8#32, 0xca492109#32]

def cw15 : List (BitVec 32) := [0x54000280#32, 0x39401028#32, 0xf100145f#32, 0x4a090108#32, 0x92401d08#32, 0xb86879a8#32, 0xca492109#32, 0x540001a0#32, 0x39401428#32, 0xf100185f#32, 0x4a090108#32, 0x92401d08#32, 0xb86879a8#32, 0xca492109#32, 0x540000c0#32, 0x39401828#32, 0x4a090108#32, 0x92401d08#32, 0xb86879a8#32, 0xca492109#32, 0xa9454ff4#32, 0xd2407d20#32, 0xa94457f6#32, 0xa9435ff8#32, 0xa94267fa#32, 0xa9416ffc#32, 0xf84607fe#32, 0xd65f03c0#32, 0x00000000#32, 0x00000000#32, 0x00000000#32, 0x00000000#32]

/-- The words of `crc32_z` in chunks of 32. -/
def codeChunks : List (List (BitVec 32)) := [cw0, cw1, cw2, cw3, cw4, cw5, cw6, cw7, cw8, cw9, cw10, cw11, cw12, cw13, cw14, cw15]

theorem codeWords_eq : wordsOf (zlibCrc32PlacedCode.drop 12) 508 ++ [0#32, 0#32, 0#32, 0#32] =
    codeChunks.flatten := by
  decide +kernel

theorem wordsOf_length : (wordsOf (zlibCrc32PlacedCode.drop 12) 508).length = 508 := by
  decide +kernel

theorem getD_flatten_chunks : ∀ (L : List (List (BitVec 32))) (c r : Nat), r < 32 →
    (∀ x ∈ L, x.length = 32) → L.flatten.getD (32 * c + r) 0#32 = (L.getD c []).getD r 0#32
  | [], _, _, _, _ => by simp
  | x :: L, 0, r, hr, h => by
    simp only [List.flatten_cons, Nat.mul_zero, Nat.zero_add, List.getD_cons_zero]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left]
    rw [h x (by simp)]; exact hr
  | x :: L, c + 1, r, hr, h => by
    simp only [List.flatten_cons, List.getD_cons_succ]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [h x (by simp)]; omega),
      h x (by simp), show 32 * (c + 1) + r - 32 = 32 * c + r by omega, ← List.getD_eq_getElem?_getD]
    exact getD_flatten_chunks L c r hr (fun y hy => h y (by simp [hy]))

theorem codeChunks_len : ∀ x ∈ codeChunks, x.length = 32 := by decide +kernel

theorem wordAt_chunk (c r : Nat) (hk : 32 * c + r < 508) (hr : r < 32) :
    zlibCrc32Text.wordAt (12 + 4 * (32 * c + r)) = (codeChunks.getD c []).getD r 0#32 := by
  have hl : (zlibCrc32PlacedCode.drop 12).length = 2812 := by rw [List.length_drop, code_length]
  rw [CodeBlock.wordAt, wordOfBytesLE_drop, show zlibCrc32Text.code = zlibCrc32PlacedCode from rfl,
    wordsOf_getD 508 _ _ hk (by omega), ← getD_flatten_chunks _ c r hr codeChunks_len,
    ← codeWords_eq, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by rw [wordsOf_length]; exact hk)]

theorem fetch_at {pl : Placement} {m : Memory} (hP : zlibCrc32Lib.Placeable pl)
    (hCL : (prog pl).CodeLoaded m) (c r : Nat) (hk : 32 * c + r < 508) (hr : r < 32) {I : Instr}
    (hrel : zlibCrc32Text.relocAt? (12 + 4 * (32 * c + r)) = none)
    (hI : decode ((codeChunks.getD c []).getD r 0#32) = some I) :
    (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (12 + 4 * (32 * c + r))) = some I := by
  rw [fetch_plain hP hCL _ (by omega) (by omega) hrel, wordAt_chunk c r hk hr, hI]

section
variable {pl : Placement} {m : Memory} (hP : zlibCrc32Lib.Placeable pl)
  (hCL : (prog pl).CodeLoaded m)
include hP hCL

theorem f_714 : (prog pl).fetchMem m (pl.base + 1824#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000000#64)) :=
  fetch_at hP hCL 14 5 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_718 : (prog pl).fetchMem m (pl.base + 1828#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x02#5) 0x001#12 false) :=
  fetch_at hP hCL 14 6 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_71c : (prog pl).fetchMem m (pl.base + 1832#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 14 7 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_720 : (prog pl).fetchMem m (pl.base + 1836#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 14 8 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_724 : (prog pl).fetchMem m (pl.base + 1840#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x08#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x08#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 14 9 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_728 : (prog pl).fetchMem m (pl.base + 1844#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 14 10 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_72c : (prog pl).fetchMem m (pl.base + 1848#64) = some (Instr.bCond (CondCode.EQ) 0x00000000000000a4#64) :=
  fetch_at hP hCL 14 11 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_730 : (prog pl).fetchMem m (pl.base + 1852#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000001#64)) :=
  fetch_at hP hCL 14 12 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_734 : (prog pl).fetchMem m (pl.base + 1856#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x02#5) 0x002#12 false) :=
  fetch_at hP hCL 14 13 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_738 : (prog pl).fetchMem m (pl.base + 1860#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 14 14 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_73c : (prog pl).fetchMem m (pl.base + 1864#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 14 15 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_740 : (prog pl).fetchMem m (pl.base + 1868#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x08#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x08#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 14 16 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_744 : (prog pl).fetchMem m (pl.base + 1872#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 14 17 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_748 : (prog pl).fetchMem m (pl.base + 1876#64) = some (Instr.bCond (CondCode.EQ) 0x0000000000000088#64) :=
  fetch_at hP hCL 14 18 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_74c : (prog pl).fetchMem m (pl.base + 1880#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000002#64)) :=
  fetch_at hP hCL 14 19 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_750 : (prog pl).fetchMem m (pl.base + 1884#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x02#5) 0x003#12 false) :=
  fetch_at hP hCL 14 20 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_754 : (prog pl).fetchMem m (pl.base + 1888#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 14 21 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_758 : (prog pl).fetchMem m (pl.base + 1892#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 14 22 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_75c : (prog pl).fetchMem m (pl.base + 1896#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x08#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x08#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 14 23 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_760 : (prog pl).fetchMem m (pl.base + 1900#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 14 24 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_764 : (prog pl).fetchMem m (pl.base + 1904#64) = some (Instr.bCond (CondCode.EQ) 0x000000000000006c#64) :=
  fetch_at hP hCL 14 25 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_768 : (prog pl).fetchMem m (pl.base + 1908#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000003#64)) :=
  fetch_at hP hCL 14 26 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_76c : (prog pl).fetchMem m (pl.base + 1912#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x02#5) 0x004#12 false) :=
  fetch_at hP hCL 14 27 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_770 : (prog pl).fetchMem m (pl.base + 1916#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 14 28 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_774 : (prog pl).fetchMem m (pl.base + 1920#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 14 29 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_778 : (prog pl).fetchMem m (pl.base + 1924#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x08#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x08#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 14 30 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_77c : (prog pl).fetchMem m (pl.base + 1928#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 14 31 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_780 : (prog pl).fetchMem m (pl.base + 1932#64) = some (Instr.bCond (CondCode.EQ) 0x0000000000000050#64) :=
  fetch_at hP hCL 15 0 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_784 : (prog pl).fetchMem m (pl.base + 1936#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000004#64)) :=
  fetch_at hP hCL 15 1 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_788 : (prog pl).fetchMem m (pl.base + 1940#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x02#5) 0x005#12 false) :=
  fetch_at hP hCL 15 2 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_78c : (prog pl).fetchMem m (pl.base + 1944#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 15 3 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_790 : (prog pl).fetchMem m (pl.base + 1948#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 15 4 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_794 : (prog pl).fetchMem m (pl.base + 1952#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x08#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x08#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 15 5 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_798 : (prog pl).fetchMem m (pl.base + 1956#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 15 6 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_79c : (prog pl).fetchMem m (pl.base + 1960#64) = some (Instr.bCond (CondCode.EQ) 0x0000000000000034#64) :=
  fetch_at hP hCL 15 7 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7a0 : (prog pl).fetchMem m (pl.base + 1964#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000005#64)) :=
  fetch_at hP hCL 15 8 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7a4 : (prog pl).fetchMem m (pl.base + 1968#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x02#5) 0x006#12 false) :=
  fetch_at hP hCL 15 9 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7a8 : (prog pl).fetchMem m (pl.base + 1972#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 15 10 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7ac : (prog pl).fetchMem m (pl.base + 1976#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 15 11 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7b0 : (prog pl).fetchMem m (pl.base + 1980#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x08#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x08#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 15 12 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7b4 : (prog pl).fetchMem m (pl.base + 1984#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 15 13 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7b8 : (prog pl).fetchMem m (pl.base + 1988#64) = some (Instr.bCond (CondCode.EQ) 0x0000000000000018#64) :=
  fetch_at hP hCL 15 14 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7bc : (prog pl).fetchMem m (pl.base + 1992#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000006#64)) :=
  fetch_at hP hCL 15 15 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7c0 : (prog pl).fetchMem m (pl.base + 1996#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 15 16 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7c4 : (prog pl).fetchMem m (pl.base + 2000#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 15 17 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7c8 : (prog pl).fetchMem m (pl.base + 2004#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x08#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x08#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 15 18 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7cc : (prog pl).fetchMem m (pl.base + 2008#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 15 19 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7d0 : (prog pl).fetchMem m (pl.base + 2012#64) = some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64)) :=
  fetch_at hP hCL 15 20 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7d4 : (prog pl).fetchMem m (pl.base + 2016#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x00#5) (Reg.gpr 0x09#5) 0x00000000ffffffff#64) :=
  fetch_at hP hCL 15 21 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7d8 : (prog pl).fetchMem m (pl.base + 2020#64) = some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x16#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64)) :=
  fetch_at hP hCL 15 22 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7dc : (prog pl).fetchMem m (pl.base + 2024#64) = some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x18#5) (Reg.gpr 0x17#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64)) :=
  fetch_at hP hCL 15 23 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7e0 : (prog pl).fetchMem m (pl.base + 2028#64) = some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1a#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x0000000000000020#64)) :=
  fetch_at hP hCL 15 24 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7e4 : (prog pl).fetchMem m (pl.base + 2032#64) = some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x1c#5) (Reg.gpr 0x1b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000010#64)) :=
  fetch_at hP hCL 15 25 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7e8 : (prog pl).fetchMem m (pl.base + 2036#64) = some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x1e#5) (AddrMode.PostIndex (Reg.sp) 0x0000000000000060#64)) :=
  fetch_at hP hCL 15 26 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_7ec : (prog pl).fetchMem m (pl.base + 2040#64) = some (Instr.ret (Reg.gpr 0x1e#5)) :=
  fetch_at hP hCL 15 27 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

end

end ZlibCrc32.Crcz
end

section
/-! # A bit-level model of zlib's braided `crc32_z` (N = 5, W = 8)

Pure functions on bit vectors that the machine-level proof shows the code computes, and whose
polynomial meaning `Solutions.ZlibCrc32Goal.Math` establishes. -/

namespace ZlibCrc32.Crcz

open Polynomial KadatchJenkins













end ZlibCrc32.Crcz
end

section
/-! # Interface of the memory / stack-frame layer (stubs proved in `PartB`) -/

namespace ZlibCrc32.Crcz

open Arm64 Arm64.Obj






section
variable {pl : Placement} {s0 : State} {R : SepProp} {m : Memory}



























end

end ZlibCrc32.Crcz
end

section
/-! # Part B: the memory / stack-frame layer (proofs of the `FrameStub` interface) -/

namespace ZlibCrc32.Crcz.PartB

open Arm64 Arm64.Obj ZlibCrc32.Crcz

/-! ## Heap cells through unions -/

/-! ## Heaps that differ only in the bytes of read-write cells of a region -/

/-! ## Memory cells -/

theorem add_ofNat_add (a : BitVec 64) (x y : ℕ) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem allPerm_of {m : Memory} {p : Option Perm → Bool} : ∀ (n : ℕ) (a : BitVec 64),
    (∀ k, k < n → p (m.perm (a + BitVec.ofNat 64 k)) = true) → m.allPerm p a n = true
  | 0, _, _ => rfl
  | n + 1, a, h => by
    simp only [Memory.allPerm, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), allPerm_of n _ fun k hk => ?_⟩
    have := h (k + 1) (by omega)
    rwa [add_ofNat_add, Nat.add_comm]

theorem allNoLazy_of {m : Memory} : ∀ (n : ℕ) (a : BitVec 64),
    (∀ k, k < n → m.isLazyFree (a + BitVec.ofNat 64 k) = false) → m.allNoLazyFree a n = true
  | 0, _, _ => rfl
  | n + 1, a, h => by
    simp only [Memory.allNoLazyFree, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨by simpa using h 0 (by omega), allNoLazy_of n _ fun k hk => ?_⟩
    have := h (k + 1) (by omega)
    rwa [add_ofNat_add, Nat.add_comm]

theorem canRead_of {m : Memory} {a : BitVec 64} {n : ℕ}
    (h : ∀ k, k < n → (m.perm (a + BitVec.ofNat 64 k)).r = true ∧
      m.isLazyFree (a + BitVec.ofNat 64 k) = false) : m.canRead a n = true := by
  simp only [Memory.canRead, Bool.and_eq_true]
  exact ⟨allPerm_of n a fun k hk => (h k hk).1, allNoLazy_of n a fun k hk => (h k hk).2⟩

/-! ## Slots of the frame -/

section
variable {s0 : State}

theorem slot_off (j k : ℕ) (hj : j < 12) (hk : k < 8) :
    (slot s0 j + BitVec.ofNat 64 k - (s0.sp - 96#64)).toNat = 8 * j + k := by
  unfold slot
  rw [BitVec.add_assoc, BitVec.add_comm (s0.sp - 96#64), BitVec.add_sub_cancel, BitVec.toNat_add, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  have : (8 * j) % 2 ^ 64 = 8 * j := Nat.mod_eq_of_lt (by omega)
  have : k % 2 ^ 64 = k := Nat.mod_eq_of_lt (by omega)
  have : (8 * j + k) % 2 ^ 64 = 8 * j + k := Nat.mod_eq_of_lt (by omega)
  simp only [*]

theorem inRegion_slot (j k : ℕ) (hj : j < 12) (hk : k < 8) :
    InRegion (s0.sp - 96#64) 96 (slot s0 j + BitVec.ofNat 64 k) := by
  unfold InRegion; rw [slot_off j k hj hk]; omega

end

/-! ## Precondition facts -/

section
variable {pl : Placement} {s0 : State} {R : SepProp} {m : Memory}

theorem frameOk_canRead (hF : FrameOk s0 m) (j : ℕ) (hj : j < 12) :
    m.canRead (slot s0 j) 8 = true := by
  refine canRead_of fun k hk => ?_
  obtain ⟨h1, h2, _⟩ := (hF _).2 (inRegion_slot j k hj hk)
  rw [h1]; exact ⟨rfl, h2⟩

theorem ro_read8 {a : BitVec 64} {bs : List (BitVec 8)} (h : RoBytes m a bs) (i : ℕ)
    (hi : i < bs.length) :
    m.canRead (a + BitVec.ofNat 64 i) 1 = true ∧ m.read8 (a + BitVec.ofNat 64 i) = bs[i] := by
  refine ⟨canRead_of fun k hk => ?_, (h i hi).1⟩
  have hk0 : k = 0 := by omega
  subst hk0
  simpa using (h i hi).2

theorem ro_read32 {a : BitVec 64} {tbl : List (BitVec 8)} (h : RoBytes m a tbl) (j : ℕ)
    (hj : 4 * j + 4 ≤ tbl.length) :
    m.canRead (a + BitVec.ofNat 64 (4 * j)) 4 = true ∧
      m.read32 (a + BitVec.ofNat 64 (4 * j)) = word32 tbl j := by
  have e : ∀ k, k < 4 → m.read8 (a + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 k) =
      tbl.getD (4 * j + k) 0#8 := fun k hk => by
    rw [add_ofNat_add, List.getD_eq_getElem _ _ (by omega)]
    exact (h _ _).1
  refine ⟨canRead_of fun k hk => ?_, ?_⟩
  · rw [add_ofNat_add]; exact (h _ (by omega)).2
  · simp only [Memory.read32, word32]
    rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega)]
    simp only [Nat.add_zero]

end

end ZlibCrc32.Crcz.PartB

namespace ZlibCrc32.Crcz
alias frameOk_canRead := PartB.frameOk_canRead
alias ro_read8 := PartB.ro_read8
alias ro_read32 := PartB.ro_read32
end ZlibCrc32.Crcz
end

section
/-! # Abstract machine states for `crc32_z` (generated by gen_machine.py)

Every state reached is `mkS s0 m sp pc ps r`: the entry state `s0` with the memory, stack
pointer, program counter, flags and the registers `x0..x28, x30` replaced (`x29` and the SIMD
registers stay those of `s0`). -/

namespace ZlibCrc32.Crcz

open Arm64 Arm64.Obj





section
variable (s0 : State) (m : Memory) (sp pc : BitVec 64) (ps : PState) (r : Regs)

@[simp] theorem mkS_mem : (mkS s0 m sp pc ps r).mem = m := rfl
@[simp] theorem mkS_pc : (mkS s0 m sp pc ps r).pc = pc := rfl
@[simp] theorem mkS_sp : (mkS s0 m sp pc ps r).sp = sp := rfl
@[simp] theorem mkS_status : (mkS s0 m sp pc ps r).status = s0.status := rfl
@[simp] theorem mkS_pstate : (mkS s0 m sp pc ps r).pstate = ps := rfl
@[simp] theorem mkS_vregs : (mkS s0 m sp pc ps r).vregs = s0.vregs := rfl
@[simp] theorem mkS_advancePC : (mkS s0 m sp pc ps r).advancePC = mkS s0 m sp (pc + 4#64) ps r := rfl
@[simp] theorem mkS_setPC (q : BitVec 64) : (mkS s0 m sp pc ps r).setPC q = mkS s0 m sp q ps r := rfl
@[simp] theorem mkS_setPState (q : PState) : (mkS s0 m sp pc ps r).setPState q = mkS s0 m sp pc q r := rfl
@[simp] theorem mkS_setMem (q : Memory) : (mkS s0 m sp pc ps r).setMem q = mkS s0 q sp pc ps r := rfl
@[simp] theorem rd_xzr : (mkS s0 m sp pc ps r).readReg64 .xzr = 0#64 := rfl
@[simp] theorem rd_sp : (mkS s0 m sp pc ps r).readReg64 .sp = sp := rfl
@[simp] theorem wr_xzr (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 .xzr v = mkS s0 m sp pc ps r := rfl
@[simp] theorem wr_sp (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 .sp v = mkS s0 m v pc ps r := rfl
@[simp] theorem rd_x29 : (mkS s0 m sp pc ps r).readReg64 (.gpr 29#5) = s0.readReg64 (.gpr 29#5) := rfl

@[simp] theorem rd_x0 : (mkS s0 m sp pc ps r).readReg64 (.gpr 0#5) = r.x0 := rfl
@[simp] theorem rd_x1 : (mkS s0 m sp pc ps r).readReg64 (.gpr 1#5) = r.x1 := rfl
@[simp] theorem rd_x2 : (mkS s0 m sp pc ps r).readReg64 (.gpr 2#5) = r.x2 := rfl
@[simp] theorem rd_x3 : (mkS s0 m sp pc ps r).readReg64 (.gpr 3#5) = r.x3 := rfl
@[simp] theorem rd_x4 : (mkS s0 m sp pc ps r).readReg64 (.gpr 4#5) = r.x4 := rfl
@[simp] theorem rd_x5 : (mkS s0 m sp pc ps r).readReg64 (.gpr 5#5) = r.x5 := rfl
@[simp] theorem rd_x6 : (mkS s0 m sp pc ps r).readReg64 (.gpr 6#5) = r.x6 := rfl
@[simp] theorem rd_x7 : (mkS s0 m sp pc ps r).readReg64 (.gpr 7#5) = r.x7 := rfl
@[simp] theorem rd_x8 : (mkS s0 m sp pc ps r).readReg64 (.gpr 8#5) = r.x8 := rfl
@[simp] theorem rd_x9 : (mkS s0 m sp pc ps r).readReg64 (.gpr 9#5) = r.x9 := rfl
@[simp] theorem rd_x10 : (mkS s0 m sp pc ps r).readReg64 (.gpr 10#5) = r.x10 := rfl
@[simp] theorem rd_x11 : (mkS s0 m sp pc ps r).readReg64 (.gpr 11#5) = r.x11 := rfl
@[simp] theorem rd_x12 : (mkS s0 m sp pc ps r).readReg64 (.gpr 12#5) = r.x12 := rfl
@[simp] theorem rd_x13 : (mkS s0 m sp pc ps r).readReg64 (.gpr 13#5) = r.x13 := rfl
@[simp] theorem rd_x14 : (mkS s0 m sp pc ps r).readReg64 (.gpr 14#5) = r.x14 := rfl
@[simp] theorem rd_x15 : (mkS s0 m sp pc ps r).readReg64 (.gpr 15#5) = r.x15 := rfl
@[simp] theorem rd_x16 : (mkS s0 m sp pc ps r).readReg64 (.gpr 16#5) = r.x16 := rfl
@[simp] theorem rd_x17 : (mkS s0 m sp pc ps r).readReg64 (.gpr 17#5) = r.x17 := rfl
@[simp] theorem rd_x18 : (mkS s0 m sp pc ps r).readReg64 (.gpr 18#5) = r.x18 := rfl
@[simp] theorem rd_x19 : (mkS s0 m sp pc ps r).readReg64 (.gpr 19#5) = r.x19 := rfl
@[simp] theorem rd_x20 : (mkS s0 m sp pc ps r).readReg64 (.gpr 20#5) = r.x20 := rfl
@[simp] theorem rd_x21 : (mkS s0 m sp pc ps r).readReg64 (.gpr 21#5) = r.x21 := rfl
@[simp] theorem rd_x22 : (mkS s0 m sp pc ps r).readReg64 (.gpr 22#5) = r.x22 := rfl
@[simp] theorem rd_x23 : (mkS s0 m sp pc ps r).readReg64 (.gpr 23#5) = r.x23 := rfl
@[simp] theorem rd_x24 : (mkS s0 m sp pc ps r).readReg64 (.gpr 24#5) = r.x24 := rfl
@[simp] theorem rd_x25 : (mkS s0 m sp pc ps r).readReg64 (.gpr 25#5) = r.x25 := rfl
@[simp] theorem rd_x26 : (mkS s0 m sp pc ps r).readReg64 (.gpr 26#5) = r.x26 := rfl
@[simp] theorem rd_x27 : (mkS s0 m sp pc ps r).readReg64 (.gpr 27#5) = r.x27 := rfl
@[simp] theorem rd_x28 : (mkS s0 m sp pc ps r).readReg64 (.gpr 28#5) = r.x28 := rfl
@[simp] theorem rd_x30 : (mkS s0 m sp pc ps r).readReg64 (.gpr 30#5) = r.x30 := rfl
@[simp] theorem wr_x0 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 0#5) v =
    mkS s0 m sp pc ps { r with x0 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 0#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x1 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 1#5) v =
    mkS s0 m sp pc ps { r with x1 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 1#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x2 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 2#5) v =
    mkS s0 m sp pc ps { r with x2 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 2#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x3 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 3#5) v =
    mkS s0 m sp pc ps { r with x3 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 3#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x4 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 4#5) v =
    mkS s0 m sp pc ps { r with x4 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 4#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x5 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 5#5) v =
    mkS s0 m sp pc ps { r with x5 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 5#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x6 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 6#5) v =
    mkS s0 m sp pc ps { r with x6 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 6#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x7 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 7#5) v =
    mkS s0 m sp pc ps { r with x7 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 7#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x8 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 8#5) v =
    mkS s0 m sp pc ps { r with x8 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 8#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x9 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 9#5) v =
    mkS s0 m sp pc ps { r with x9 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 9#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x10 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 10#5) v =
    mkS s0 m sp pc ps { r with x10 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 10#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x11 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 11#5) v =
    mkS s0 m sp pc ps { r with x11 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 11#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x12 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 12#5) v =
    mkS s0 m sp pc ps { r with x12 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 12#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x13 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 13#5) v =
    mkS s0 m sp pc ps { r with x13 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 13#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x14 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 14#5) v =
    mkS s0 m sp pc ps { r with x14 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 14#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x15 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 15#5) v =
    mkS s0 m sp pc ps { r with x15 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 15#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x16 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 16#5) v =
    mkS s0 m sp pc ps { r with x16 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 16#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x17 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 17#5) v =
    mkS s0 m sp pc ps { r with x17 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 17#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x18 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 18#5) v =
    mkS s0 m sp pc ps { r with x18 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 18#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x19 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 19#5) v =
    mkS s0 m sp pc ps { r with x19 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 19#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x20 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 20#5) v =
    mkS s0 m sp pc ps { r with x20 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 20#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x21 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 21#5) v =
    mkS s0 m sp pc ps { r with x21 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 21#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x22 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 22#5) v =
    mkS s0 m sp pc ps { r with x22 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 22#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x23 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 23#5) v =
    mkS s0 m sp pc ps { r with x23 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 23#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x24 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 24#5) v =
    mkS s0 m sp pc ps { r with x24 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 24#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x25 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 25#5) v =
    mkS s0 m sp pc ps { r with x25 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 25#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x26 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 26#5) v =
    mkS s0 m sp pc ps { r with x26 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 26#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x27 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 27#5) v =
    mkS s0 m sp pc ps { r with x27 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 27#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x28 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 28#5) v =
    mkS s0 m sp pc ps { r with x28 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 28#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]
@[simp] theorem wr_x30 (v : BitVec 64) : (mkS s0 m sp pc ps r).writeReg64 (.gpr 30#5) v =
    mkS s0 m sp pc ps { r with x30 := v } := by
  simp only [mkS, State.writeReg64, RegFile.write, State.mk.injEq]
  rw [if_neg (by decide)]
  refine ⟨?_, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial⟩
  congr 1; funext i
  by_cases h : i = 30#5
  · subst h; simp [Regs.get]
  · simp only [h, if_false]; simp only [Regs.get]; simp [h]

end

end ZlibCrc32.Crcz
end

section
/-! # Steps, `Reach`, and the per-constructor execution lemmas -/

namespace ZlibCrc32.Crcz

open Arm64 Arm64.Obj

theorem step_of {pl : Placement} {s : State} {inst : Instr} (hrun : s.status = .Running)
    (hf : (prog pl).fetchMem s.mem s.pc = some inst) :
    Step (prog pl) s (execInstWithSvc (evalSvc Syscall.standard) inst s) := by
  have := Step.exec (prog := prog pl) hrun hf
  rw [Program.evalInst] at this
  rwa [show (prog pl).svc = Syscall.standard from rfl] at this

/-- One step from an abstract state. -/
theorem stepM {pl : Placement} {s0 : State} {m : Memory} {sp pc : BitVec 64} {ps : PState}
    {r : Regs} {inst : Instr} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc = some inst) :
    Step (prog pl) (mkS s0 m sp pc ps r)
      (execInstWithSvc (evalSvc Syscall.standard) inst (mkS s0 m sp pc ps r)) :=
  step_of (s := mkS s0 m sp pc ps r) hrun hf



theorem reach_step {pl : Placement} {s0 s s' : State} {X : BitVec 64} (h : Step (prog pl) s s')
    (h' : Reach pl s0 X s') : Reach pl s0 X s := by
  obtain ⟨sf, h1, h2⟩ := h'
  exact ⟨sf, Steps.step h h1, h2⟩

section
variable (svc : State → State) (s : State)
theorem ex_addSubImm (w : RegWidth) (op : AddSubOp) (rd rn : Reg) (imm : BitVec 12) (sh : Bool) :
    execInstWithSvc svc (.addSubImm w op rd rn imm sh) s = execAddSubImm w op rd rn imm sh s := rfl
theorem ex_logicalShift (w : RegWidth) (op : LogicalOp) (rd rn rm : Reg) (sh : ShiftType) (a : Nat) :
    execInstWithSvc svc (.logicalShift w op rd rn rm sh a) s = execLogicalShift w op rd rn rm sh a s := rfl
theorem ex_logicalImm (w : RegWidth) (op : LogicalOp) (rd rn : Reg) (mask : BitVec 64) :
    execInstWithSvc svc (.logicalImm w op rd rn mask) s = execLogicalImm w op rd rn mask s := rfl
theorem ex_bCond (c : CondCode) (off : BitVec 64) :
    execInstWithSvc svc (.bCond c off) s =
      if ConditionHolds c s.pstate then s.setPC (s.pc + off) else s.advancePC := rfl
theorem ex_ldr (w : RegWidth) (sz : MemWidth) (sg : Bool) (rt : Reg) (a : AddrMode) :
    execInstWithSvc svc (.ldr w sz sg rt a) s = execLdr w sz sg rt a s := rfl
theorem ex_ldp (w : RegWidth) (sg : Bool) (rt1 rt2 : Reg) (a : AddrMode) :
    execInstWithSvc svc (.ldp w sg rt1 rt2 a) s = execLdp w sg rt1 rt2 a s := rfl
theorem ex_ret (rn : Reg) : execInstWithSvc svc (.ret rn) s = s.setPC (s.readReg64 rn) := rfl
end

end ZlibCrc32.Crcz
end

section
namespace ZlibCrc32.Crcz

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Arm64 Arm64.Obj


/-- Slot `j` of the frame in simp-normal form. -/
theorem slot_eq (s0 : State) (j : ℕ) (hj : j < 12) :
    slot s0 j = s0.sp + BitVec.ofNat 64 (18446744073709551520 + 8 * j) := by
  simp only [slot]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_sub]; omega


theorem and15_toNat (x : BitVec 64) : (x &&& 15#64).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem aligned_add (x : BitVec 64) (k : ℕ) (hk : k % 16 = 0)
    (h : (x &&& 15#64 == 0#64) = true) : ((x + BitVec.ofNat 64 k) &&& 15#64 == 0#64) = true := by
  rw [beq_iff_eq, ← BitVec.toNat_inj, and15_toNat] at h ⊢
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_zero] at h ⊢
  omega

theorem fin_val (c : BitVec 32) : c.setWidth 64 ^^^ 4294967295#64 = (~~~c).setWidth 64 := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (4294967295#64 : BitVec 64) = (BitVec.allOnes 32).setWidth 64 := by decide
  rw [h1, ← BitVec.setWidth_xor, BitVec.xor_allOnes]

/-- Returning: the state at the caller's return address satisfies `Fin`. -/
theorem fin_mkS {pl : Placement} {s0 : State} {m : Memory} {ps : PState} {r : Regs} {X : BitVec 64}
    (hrun : s0.status = .Running) (hF : FrameOk s0 m)
    (h19 : r.x19 = s0.readReg64 (.gpr 19#5)) (h20 : r.x20 = s0.readReg64 (.gpr 20#5))
    (h21 : r.x21 = s0.readReg64 (.gpr 21#5)) (h22 : r.x22 = s0.readReg64 (.gpr 22#5))
    (h23 : r.x23 = s0.readReg64 (.gpr 23#5)) (h24 : r.x24 = s0.readReg64 (.gpr 24#5))
    (h25 : r.x25 = s0.readReg64 (.gpr 25#5)) (h26 : r.x26 = s0.readReg64 (.gpr 26#5))
    (h27 : r.x27 = s0.readReg64 (.gpr 27#5)) (h28 : r.x28 = s0.readReg64 (.gpr 28#5))
    (h0 : r.x0 = X) :
    Reach pl s0 X (mkS s0 m s0.sp (s0.readReg64 (.gpr 30#5)) ps r) :=
  ⟨_, Steps.refl _, rfl, rfl, hrun, ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, rfl, rfl⟩, h0, hF⟩

set_option maxHeartbeats 1000000 in
theorem epi {pl : Placement} {s0 : State} {m : Memory} {ps : PState} {r : Regs}
    (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded m) (hrun : s0.status = .Running)
    (hal : s0.spAligned = true) (hF : FrameOk s0 m) (hS : Saved s0 m) (c : BitVec 32)
    (h9 : r.x9 = c.setWidth 64) :
    Reach pl s0 ((~~~c).setWidth 64) (mkS s0 m (spIn s0) (pl.base + 2012#64) ps r) := by
  have hal' : (spIn s0 &&& 15#64 == 0#64) = true := by
    exact aligned_add s0.sp _ (by decide) hal
  have rd := fun j hj => frameOk_canRead hF j hj
  rw [Saved, slot_eq s0 0 (by decide), slot_eq s0 2 (by decide), slot_eq s0 3 (by decide),
    slot_eq s0 4 (by decide), slot_eq s0 5 (by decide), slot_eq s0 6 (by decide),
    slot_eq s0 7 (by decide), slot_eq s0 8 (by decide), slot_eq s0 9 (by decide),
    slot_eq s0 10 (by decide), slot_eq s0 11 (by decide)] at hS
  simp only [Nat.reduceMul, Nat.reduceAdd] at hS
  obtain ⟨s0', s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := hS
  have c10 := rd 10 (by decide); have c11 := rd 11 (by decide)
  rw [slot_eq s0 _ (by decide)] at c10 c11
  simp only [Nat.reduceMul, Nat.reduceAdd] at c10 c11
  have c0 := rd 0 (by decide); have c2 := rd 2 (by decide); have c3 := rd 3 (by decide)
  have c4 := rd 4 (by decide); have c5 := rd 5 (by decide); have c6 := rd 6 (by decide)
  have c7 := rd 7 (by decide); have c8 := rd 8 (by decide); have c9 := rd 9 (by decide)
  rw [slot_eq s0 _ (by decide)] at c0 c2 c3 c4 c5 c6 c7 c8 c9
  simp only [Nat.reduceMul, Nat.reduceAdd] at c0 c2 c3 c4 c5 c6 c7 c8 c9
  refine reach_step (stepM hrun (f_7d0 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, evalLogical, ex_ret,
    checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned, mkS_sp, hal',
    evalAddrMode, rd_sp, BitVec.add_assoc, BitVec.reduceAdd, Bool.false_eq_true, Bool.not_true,
    if_false, MemWidth.bytes, mkS_mem, Bool.and_self, Memory.readSized, State.writeReg,
    State.readReg, mkS_advancePC, mkS_setPC, wr_sp, rd_x9, wr_x0, rd_x30, wr_x30,
    wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, c10, c11, s10, s11]
  refine reach_step (stepM hrun (f_7d4 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, evalLogical, ex_ret,
    checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned, mkS_sp, hal',
    evalAddrMode, rd_sp, BitVec.add_assoc, BitVec.reduceAdd, Bool.false_eq_true, Bool.not_true,
    if_false, MemWidth.bytes, mkS_mem, Bool.and_self, Memory.readSized, State.writeReg,
    State.readReg, mkS_advancePC, mkS_setPC, wr_sp, rd_x9, wr_x0, rd_x30, wr_x30,
    wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28]
  refine reach_step (stepM hrun (f_7d8 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, evalLogical, ex_ret,
    checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned, mkS_sp, hal',
    evalAddrMode, rd_sp, BitVec.add_assoc, BitVec.reduceAdd, Bool.false_eq_true, Bool.not_true,
    if_false, MemWidth.bytes, mkS_mem, Bool.and_self, Memory.readSized, State.writeReg,
    State.readReg, mkS_advancePC, mkS_setPC, wr_sp, rd_x9, wr_x0, rd_x30, wr_x30,
    wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, c8, c9, s8, s9]
  refine reach_step (stepM hrun (f_7dc hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, evalLogical, ex_ret,
    checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned, mkS_sp, hal',
    evalAddrMode, rd_sp, BitVec.add_assoc, BitVec.reduceAdd, Bool.false_eq_true, Bool.not_true,
    if_false, MemWidth.bytes, mkS_mem, Bool.and_self, Memory.readSized, State.writeReg,
    State.readReg, mkS_advancePC, mkS_setPC, wr_sp, rd_x9, wr_x0, rd_x30, wr_x30,
    wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, c6, c7, s6, s7]
  refine reach_step (stepM hrun (f_7e0 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, evalLogical, ex_ret,
    checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned, mkS_sp, hal',
    evalAddrMode, rd_sp, BitVec.add_assoc, BitVec.reduceAdd, Bool.false_eq_true, Bool.not_true,
    if_false, MemWidth.bytes, mkS_mem, Bool.and_self, Memory.readSized, State.writeReg,
    State.readReg, mkS_advancePC, mkS_setPC, wr_sp, rd_x9, wr_x0, rd_x30, wr_x30,
    wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, c4, c5, s4, s5]
  refine reach_step (stepM hrun (f_7e4 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, evalLogical, ex_ret,
    checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned, mkS_sp, hal',
    evalAddrMode, rd_sp, BitVec.add_assoc, BitVec.reduceAdd, Bool.false_eq_true, Bool.not_true,
    if_false, MemWidth.bytes, mkS_mem, Bool.and_self, Memory.readSized, State.writeReg,
    State.readReg, mkS_advancePC, mkS_setPC, wr_sp, rd_x9, wr_x0, rd_x30, wr_x30,
    wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, c2, c3, s2, s3]
  refine reach_step (stepM hrun (f_7e8 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, evalLogical, ex_ret,
    checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned, mkS_sp, hal',
    evalAddrMode, rd_sp, BitVec.add_assoc, BitVec.reduceAdd, Bool.false_eq_true, Bool.not_true,
    if_false, MemWidth.bytes, mkS_mem, Bool.and_self, Memory.readSized, State.writeReg,
    State.readReg, mkS_advancePC, mkS_setPC, wr_sp, rd_x9, wr_x0, rd_x30, wr_x30,
    wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, c0, s0']
  refine reach_step (stepM hrun (f_7ec hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, evalLogical, ex_ret,
    checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned, mkS_sp, hal',
    evalAddrMode, rd_sp, BitVec.add_assoc, BitVec.reduceAdd, Bool.false_eq_true, Bool.not_true,
    if_false, MemWidth.bytes, mkS_mem, Bool.and_self, Memory.readSized, State.writeReg,
    State.readReg, mkS_advancePC, mkS_setPC, wr_sp, rd_x9, wr_x0, rd_x30, wr_x30,
    wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28]
  rw [BitVec.add_zero]
  exact fin_mkS hrun hF rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl (by rw [h9, fin_val])

end ZlibCrc32.Crcz
end

section
/-! # Blueprint: the blocks of `crc32_z` as `Reach` lemmas (stubs proved in Parts) -/

namespace ZlibCrc32.Crcz

set_option linter.unusedVariables false

open Arm64 Arm64.Obj


section
variable {pl : Placement} {s0 : State} {bs : List (BitVec 8)} {m : Memory} {ps : PState}
  {R : Regs}



















end

end ZlibCrc32.Crcz
end

section
/-! # Flags of `cmp`/`subs`, and small shared helpers -/

namespace ZlibCrc32.Crcz

open Arm64 Arm64.Obj

theorem awc_z (x y : BitVec 64) : (AddWithCarry64 x (~~~y) true).2.z = decide (x.toNat = y.toNat) := by
  simp only [AddWithCarry64, if_true]
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [← BitVec.toNat_inj]
  simp [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_not]
  omega

theorem cond_EQ (x y : BitVec 64) :
    ConditionHolds .EQ (AddWithCarry64 x (~~~y) true).2 = decide (x.toNat = y.toNat) := by
  simp only [ConditionHolds, awc_z]

theorem toNat_ofNat_lt (r : ℕ) (hr : r < 2 ^ 64) : (BitVec.ofNat 64 r).toNat = r :=
  Nat.mod_eq_of_lt hr

end ZlibCrc32.Crcz
end

section
/-! # Part T: the byte-wise blocks (tail at `0x714`, 8-byte loop at `0x658`) -/

namespace ZlibCrc32.Crcz.PartT

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Arm64 Arm64.Obj ZlibCrc32.Crcz

theorem len0 : zlibCrc32PlacedData0.length = 1024 := by decide +kernel

theorem tz (a : BitVec 32) : (a.setWidth 64).setWidth 32 = a := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

/-- `ldr wT, [x13, xI, lsl #2]` from `crc_table`. -/
theorem ldrT0 {pl : Placement} {s0 : State} {m : Memory} {sp pc : BitVec 64} {ps : PState}
    {r : Regs} {X : BitVec 64} {rt rb ri : BitVec 5} {T : BitVec 64}
    (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc =
      some (.ldr .W32 .W32 false (.gpr rt) (.RegOffset (.gpr rb) (.gpr ri) .UXTX 2)))
    (hT : RoBytes m T zlibCrc32PlacedData0)
    (hb : (mkS s0 m sp pc ps r).readReg64 (.gpr rb) = T)
    (hi : ((mkS s0 m sp pc ps r).readReg64 (.gpr ri)).toNat < 256)
    (h : Reach pl s0 X (((mkS s0 m sp pc ps r).writeReg64 (.gpr rt)
      ((T0 ((mkS s0 m sp pc ps r).readReg64 (.gpr ri)).toNat).setWidth 64)).advancePC)) :
    Reach pl s0 X (mkS s0 m sp pc ps r) := by
  refine reach_step (stepM hrun hf) ?_
  have hm : (mkS s0 m sp pc ps r).mem = m := rfl
  generalize mkS s0 m sp pc ps r = s at hb hi h hm ⊢
  subst hm
  generalize hidef : s.readReg64 (.gpr ri) = i at hi h
  obtain ⟨hc, hv⟩ := ro_read32 hT i.toNat (by rw [len0]; omega)
  have haddr : s.readReg64 (.gpr rb) + extendVal .W64 i .UXTX 2 =
      T + BitVec.ofNat 64 (4 * i.toNat) := by
    rw [hb]; apply BitVec.eq_of_toNat_eq
    simp only [extendVal, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]
    omega
  simp only [ex_ldr, execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned,
    evalAddrMode, hidef, haddr, hc, Bool.not_true, Bool.false_eq_true, if_false, MemWidth.bytes,
    Memory.readSized, hv, State.writeReg]
  rw [show (BitVec.truncate 32 (BitVec.zeroExtend 64 (word32 zlibCrc32PlacedData0 i.toNat))) =
    T0 i.toNat from tz _]
  exact h

theorem idx_and (x : BitVec 64) : (x &&& 255#64).toNat < 256 := by
  rw [BitVec.toNat_and]; exact lt_of_le_of_lt Nat.and_le_right (by decide)

theorem toNat_and255 (x : BitVec 64) : (x &&& 255#64).toNat = x.toNat % 256 := by
  rw [BitVec.toNat_and, show (255#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem xor_sw (a b : BitVec 32) : a.setWidth 64 ^^^ b.setWidth 64 = (a ^^^ b).setWidth 64 := by
  rw [BitVec.setWidth_xor]

theorem sw32 (x : BitVec 32) : (x.setWidth 64).setWidth 32 = x := by simp
theorem sw8 (b : BitVec 8) : (b.setWidth 64).setWidth 32 = b.setWidth 32 := by simp

theorem tval (b : BitVec 8) (c : BitVec 32) :
    (T0 ((BitVec.setWidth 64 (BitVec.setWidth 32 b ^^^ c) &&& 255#64).toNat)).setWidth 64 ^^^
      (c.setWidth 64 >>> 8) = (tstep c b).setWidth 64 := by
  have hi : (BitVec.setWidth 64 (BitVec.setWidth 32 b ^^^ c) &&& 255#64).toNat =
      (c ^^^ b.setWidth 32).toNat % 256 := by
    rw [toNat_and255, BitVec.xor_comm, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (lt_of_lt_of_le (BitVec.isLt _) (by norm_num))]
  have hs : c.setWidth 64 >>> 8 = (c >>> 8).setWidth 64 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  rw [hi, hs, tstep, BitVec.setWidth_xor]

theorem pc_add (b : BitVec 64) (n k : Nat) :
    b + BitVec.ofNat 64 n + BitVec.ofNat 64 k = b + BitVec.ofNat 64 (n + k) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

set_option maxHeartbeats 1000000 in
/-- Table round: `eor w8, w8, w9; and x8, x8, #0xff; ldr w8, [x13, x8, lsl #2];
eor x9, x8, x9, lsr #8`. -/
theorem roundT {pl : Placement} {s0 : State} {bs : List (BitVec 8)} {m : Memory} {sp : BitVec 64}
    {ps : PState} {R : Regs} {X : BitVec 64} (hE : Env pl s0 bs m) (hCL : (prog pl).CodeLoaded m) (N : ℕ)
    (f0 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 N) =
      some (.logicalShift .W32 .EOR (.gpr 8#5) (.gpr 8#5) (.gpr 9#5) .LSL 0))
    (f1 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 4)) =
      some (.logicalImm .W64 .AND (.gpr 8#5) (.gpr 8#5) 0xff#64))
    (f2 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 4 + 4)) =
      some (.ldr .W32 .W32 false (.gpr 8#5) (.RegOffset (.gpr 13#5) (.gpr 8#5) .UXTX 2)))
    (f3 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 4 + 4 + 4)) =
      some (.logicalShift .W64 .EOR (.gpr 9#5) (.gpr 8#5) (.gpr 9#5) .LSR 8))
    (b : BitVec 8) (c : BitVec 32) (hb : R.x8 = (b.setWidth 32).setWidth 64)
    (hc : R.x9 = c.setWidth 64) (h13 : R.x13 = pl.ρ crcTabSym)
    (h : ∀ v : BitVec 64, Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 (N + 4 + 4 + 4 + 4)) ps
      { R with x8 := v, x9 := (tstep c b).setWidth 64 })) :
    Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 N) ps R) := by
  have hrun := hE.hrun
  refine reach_step (stepM hrun f0) ?_
  simp only [ex_logicalShift, execLogicalShift, evalLogical, shiftVal, shift32, State.readReg,
    State.readReg32, rd_x8, rd_x9, hb, hc, State.writeReg, wr_x8, mkS_advancePC, Bool.false_eq_true,
    if_false, ite_false, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.truncate_eq_setWidth,
    BitVec.zeroExtend_eq_setWidth, xor_sw, sw32, sw8, pc_add]
  refine reach_step (stepM hrun f1) ?_
  simp only [ex_logicalImm, execLogicalImm, evalLogical, State.readReg, rd_x8, State.writeReg,
    wr_x8, mkS_advancePC, Bool.false_eq_true, if_false, ite_false, pc_add, BitVec.truncate_eq_setWidth,
    BitVec.zeroExtend_eq_setWidth]
  refine ldrT0 hrun f2 hE.hT (by simp [h13])
    (by simp only [rd_x8]; exact idx_and _) ?_
  simp only [rd_x8, wr_x8, mkS_advancePC, pc_add]
  refine reach_step (stepM hrun f3) ?_
  simp only [ex_logicalShift, execLogicalShift, evalLogical, shiftVal, shift64, State.readReg,
    rd_x8, rd_x9, hc, State.writeReg, wr_x9, mkS_advancePC, Bool.false_eq_true, if_false, ite_false,
    Nat.reduceMod, tval, pc_add]
  simpa only [hb, hc] using h _

theorem cb_step {bs : List (BitVec 8)} (c : BitVec 32) (i j : ℕ) (h : i < bs.length) (hj : j = i + 1) :
    crcBytes c (bs.drop i) = crcBytes (tstep c bs[i]) (bs.drop j) := by
  subst hj; rw [List.drop_eq_getElem_cons h]; rfl

theorem cb_end {bs : List (BitVec 8)} {p : ℕ} (c : BitVec 32) (h : bs.length ≤ p) :
    crcBytes c (bs.drop p) = c := by
  rw [List.drop_eq_nil_of_le h]; rfl


end ZlibCrc32.Crcz.PartT
end

section
namespace ZlibCrc32.Crcz.PartT

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Arm64 Arm64.Obj ZlibCrc32.Crcz

section
variable {pl : Placement} {s0 : State} {bs : List (BitVec 8)} {m : Memory} {ps : PState}
  {R : Regs}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem tail (hE : Env pl s0 bs m) (c : BitVec 32) (p r : ℕ) (hpr : p + r = bs.length)
    (hr1 : 1 ≤ r) (hr7 : r ≤ 7)
    (h1 : R.x1 = s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 p) (h2 : R.x2 = BitVec.ofNat 64 r)
    (h9 : R.x9 = c.setWidth 64) (h13 : R.x13 = pl.ρ crcTabSym) :
    Reach pl s0 ((~~~ crcBytes c (bs.drop p)).setWidth 64)
      (mkS s0 m (spIn s0) (pl.base + 1824#64) ps R) := by
  have hP := hE.hP; have hCL := hE.hCL; have hrun := hE.hrun; have hn := hE.hlen
  have hr2 : ∀ k : ℕ, k < 2 ^ 64 → ((BitVec.ofNat 64 r).toNat = (BitVec.ofNat 64 k).toNat) = (r = k) := by
    intro k hk; rw [toNat_ofNat_lt _ (by omega), toNat_ofNat_lt _ hk]
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18,
    y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y30⟩ := R
  simp only at h1 h2 h9 h13
  subst h1 h2 h9 h13

  -- byte 0
  obtain ⟨cr0, rb0⟩ := ro_read8 hE.hbuf (p) (by omega)
  refine reach_step (stepM hrun (f_714 hP hCL)) ?_
  simp only [ex_ldr, execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode,
      rd_x1, BitVec.add_zero, MemWidth.bytes, Memory.readSized, Bool.not_true, Bool.false_eq_true,
      if_false, ite_false, State.writeReg, wr_x8, wr_x9, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd,
      mkS_mem, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, sw8, cr0, rb0]
  refine reach_step (stepM hrun (f_718 hP hCL)) ?_
  simp only [ex_addSubImm, execAddSubImm, State.readReg, rd_x2, evalAddSub, State.writeReg,
      wr_xzr, mkS_setPState, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, ite_true,
      ite_false, Bool.false_eq_true, BitVec.reduceZeroExtend]
  refine roundT hE hCL 1832 (f_71c hP hCL) (f_720 hP hCL) (f_724 hP hCL) (f_728 hP hCL) bs[p] c rfl rfl rfl (fun v => ?_)
  rw [cb_step c (p) (p + 1) (by omega) (by omega)]
  simp only [Nat.reduceAdd]
  refine reach_step (stepM hrun (f_72c hP hCL)) ?_
  by_cases hk0 : r = 1
  · simp only [ex_bCond, mkS_pstate, mkS_pc, cond_EQ, hr2, mkS_setPC, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, hk0, decide_true, if_true, show (1 : ℕ) < 2 ^ 64 by norm_num]
    rw [cb_end _ (by omega)]
    refine epi hP hCL hrun hE.hal hE.hF hE.hS _ ?_; rfl
  simp only [ex_bCond, mkS_pstate, mkS_pc, cond_EQ, hr2, mkS_setPC, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, hk0, decide_false, Bool.false_eq_true, if_false, show (1 : ℕ) < 2 ^ 64 by norm_num]
  -- byte 1
  obtain ⟨cr1, rb1⟩ := ro_read8 hE.hbuf (p + 1) (by omega)
  rw [BitVec.ofNat_add] at cr1 rb1
  refine reach_step (stepM hrun (f_730 hP hCL)) ?_
  simp only [ex_ldr, execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode,
      rd_x1, BitVec.add_zero, MemWidth.bytes, Memory.readSized, Bool.not_true, Bool.false_eq_true,
      if_false, ite_false, State.writeReg, wr_x8, wr_x9, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd,
      mkS_mem, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, sw8, cr1, rb1]
  refine reach_step (stepM hrun (f_734 hP hCL)) ?_
  simp only [ex_addSubImm, execAddSubImm, State.readReg, rd_x2, evalAddSub, State.writeReg,
      wr_xzr, mkS_setPState, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, ite_true,
      ite_false, Bool.false_eq_true, BitVec.reduceZeroExtend]
  refine roundT hE hCL 1860 (f_738 hP hCL) (f_73c hP hCL) (f_740 hP hCL) (f_744 hP hCL) bs[p + 1] (tstep c bs[p]) rfl rfl rfl (fun v => ?_)
  rw [cb_step (tstep c bs[p]) (p + 1) (p + 2) (by omega) (by omega)]
  simp only [Nat.reduceAdd]
  refine reach_step (stepM hrun (f_748 hP hCL)) ?_
  by_cases hk1 : r = 2
  · simp only [ex_bCond, mkS_pstate, mkS_pc, cond_EQ, hr2, mkS_setPC, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, hk1, decide_true, if_true, show (2 : ℕ) < 2 ^ 64 by norm_num]
    rw [cb_end _ (by omega)]
    refine epi hP hCL hrun hE.hal hE.hF hE.hS _ ?_; rfl
  simp only [ex_bCond, mkS_pstate, mkS_pc, cond_EQ, hr2, mkS_setPC, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, hk1, decide_false, Bool.false_eq_true, if_false, show (2 : ℕ) < 2 ^ 64 by norm_num]
  -- byte 2
  obtain ⟨cr2, rb2⟩ := ro_read8 hE.hbuf (p + 2) (by omega)
  rw [BitVec.ofNat_add] at cr2 rb2
  refine reach_step (stepM hrun (f_74c hP hCL)) ?_
  simp only [ex_ldr, execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode,
      rd_x1, BitVec.add_zero, MemWidth.bytes, Memory.readSized, Bool.not_true, Bool.false_eq_true,
      if_false, ite_false, State.writeReg, wr_x8, wr_x9, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd,
      mkS_mem, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, sw8, cr2, rb2]
  refine reach_step (stepM hrun (f_750 hP hCL)) ?_
  simp only [ex_addSubImm, execAddSubImm, State.readReg, rd_x2, evalAddSub, State.writeReg,
      wr_xzr, mkS_setPState, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, ite_true,
      ite_false, Bool.false_eq_true, BitVec.reduceZeroExtend]
  refine roundT hE hCL 1888 (f_754 hP hCL) (f_758 hP hCL) (f_75c hP hCL) (f_760 hP hCL) bs[p + 2] (tstep (tstep c bs[p]) bs[p + 1]) rfl rfl rfl (fun v => ?_)
  rw [cb_step (tstep (tstep c bs[p]) bs[p + 1]) (p + 2) (p + 3) (by omega) (by omega)]
  simp only [Nat.reduceAdd]
  refine reach_step (stepM hrun (f_764 hP hCL)) ?_
  by_cases hk2 : r = 3
  · simp only [ex_bCond, mkS_pstate, mkS_pc, cond_EQ, hr2, mkS_setPC, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, hk2, decide_true, if_true, show (3 : ℕ) < 2 ^ 64 by norm_num]
    rw [cb_end _ (by omega)]
    refine epi hP hCL hrun hE.hal hE.hF hE.hS _ ?_; rfl
  simp only [ex_bCond, mkS_pstate, mkS_pc, cond_EQ, hr2, mkS_setPC, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, hk2, decide_false, Bool.false_eq_true, if_false, show (3 : ℕ) < 2 ^ 64 by norm_num]
  -- byte 3
  obtain ⟨cr3, rb3⟩ := ro_read8 hE.hbuf (p + 3) (by omega)
  rw [BitVec.ofNat_add] at cr3 rb3
  refine reach_step (stepM hrun (f_768 hP hCL)) ?_
  simp only [ex_ldr, execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode,
      rd_x1, BitVec.add_zero, MemWidth.bytes, Memory.readSized, Bool.not_true, Bool.false_eq_true,
      if_false, ite_false, State.writeReg, wr_x8, wr_x9, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd,
      mkS_mem, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, sw8, cr3, rb3]
  refine reach_step (stepM hrun (f_76c hP hCL)) ?_
  simp only [ex_addSubImm, execAddSubImm, State.readReg, rd_x2, evalAddSub, State.writeReg,
      wr_xzr, mkS_setPState, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, ite_true,
      ite_false, Bool.false_eq_true, BitVec.reduceZeroExtend]
  refine roundT hE hCL 1916 (f_770 hP hCL) (f_774 hP hCL) (f_778 hP hCL) (f_77c hP hCL) bs[p + 3] (tstep (tstep (tstep c bs[p]) bs[p + 1]) bs[p + 2]) rfl rfl rfl (fun v => ?_)
  rw [cb_step (tstep (tstep (tstep c bs[p]) bs[p + 1]) bs[p + 2]) (p + 3) (p + 4) (by omega) (by omega)]
  simp only [Nat.reduceAdd]
  refine reach_step (stepM hrun (f_780 hP hCL)) ?_
  by_cases hk3 : r = 4
  · simp only [ex_bCond, mkS_pstate, mkS_pc, cond_EQ, hr2, mkS_setPC, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, hk3, decide_true, if_true, show (4 : ℕ) < 2 ^ 64 by norm_num]
    rw [cb_end _ (by omega)]
    refine epi hP hCL hrun hE.hal hE.hF hE.hS _ ?_; rfl
  simp only [ex_bCond, mkS_pstate, mkS_pc, cond_EQ, hr2, mkS_setPC, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, hk3, decide_false, Bool.false_eq_true, if_false, show (4 : ℕ) < 2 ^ 64 by norm_num]
  -- byte 4
  obtain ⟨cr4, rb4⟩ := ro_read8 hE.hbuf (p + 4) (by omega)
  rw [BitVec.ofNat_add] at cr4 rb4
  refine reach_step (stepM hrun (f_784 hP hCL)) ?_
  simp only [ex_ldr, execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode,
      rd_x1, BitVec.add_zero, MemWidth.bytes, Memory.readSized, Bool.not_true, Bool.false_eq_true,
      if_false, ite_false, State.writeReg, wr_x8, wr_x9, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd,
      mkS_mem, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, sw8, cr4, rb4]
  refine reach_step (stepM hrun (f_788 hP hCL)) ?_
  simp only [ex_addSubImm, execAddSubImm, State.readReg, rd_x2, evalAddSub, State.writeReg,
      wr_xzr, mkS_setPState, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, ite_true,
      ite_false, Bool.false_eq_true, BitVec.reduceZeroExtend]
  refine roundT hE hCL 1944 (f_78c hP hCL) (f_790 hP hCL) (f_794 hP hCL) (f_798 hP hCL) bs[p + 4] (tstep (tstep (tstep (tstep c bs[p]) bs[p + 1]) bs[p + 2]) bs[p + 3]) rfl rfl rfl (fun v => ?_)
  rw [cb_step (tstep (tstep (tstep (tstep c bs[p]) bs[p + 1]) bs[p + 2]) bs[p + 3]) (p + 4) (p + 5) (by omega) (by omega)]
  simp only [Nat.reduceAdd]
  refine reach_step (stepM hrun (f_79c hP hCL)) ?_
  by_cases hk4 : r = 5
  · simp only [ex_bCond, mkS_pstate, mkS_pc, cond_EQ, hr2, mkS_setPC, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, hk4, decide_true, if_true, show (5 : ℕ) < 2 ^ 64 by norm_num]
    rw [cb_end _ (by omega)]
    refine epi hP hCL hrun hE.hal hE.hF hE.hS _ ?_; rfl
  simp only [ex_bCond, mkS_pstate, mkS_pc, cond_EQ, hr2, mkS_setPC, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, hk4, decide_false, Bool.false_eq_true, if_false, show (5 : ℕ) < 2 ^ 64 by norm_num]
  -- byte 5
  obtain ⟨cr5, rb5⟩ := ro_read8 hE.hbuf (p + 5) (by omega)
  rw [BitVec.ofNat_add] at cr5 rb5
  refine reach_step (stepM hrun (f_7a0 hP hCL)) ?_
  simp only [ex_ldr, execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode,
      rd_x1, BitVec.add_zero, MemWidth.bytes, Memory.readSized, Bool.not_true, Bool.false_eq_true,
      if_false, ite_false, State.writeReg, wr_x8, wr_x9, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd,
      mkS_mem, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, sw8, cr5, rb5]
  refine reach_step (stepM hrun (f_7a4 hP hCL)) ?_
  simp only [ex_addSubImm, execAddSubImm, State.readReg, rd_x2, evalAddSub, State.writeReg,
      wr_xzr, mkS_setPState, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, ite_true,
      ite_false, Bool.false_eq_true, BitVec.reduceZeroExtend]
  refine roundT hE hCL 1972 (f_7a8 hP hCL) (f_7ac hP hCL) (f_7b0 hP hCL) (f_7b4 hP hCL) bs[p + 5] (tstep (tstep (tstep (tstep (tstep c bs[p]) bs[p + 1]) bs[p + 2]) bs[p + 3]) bs[p + 4]) rfl rfl rfl (fun v => ?_)
  rw [cb_step (tstep (tstep (tstep (tstep (tstep c bs[p]) bs[p + 1]) bs[p + 2]) bs[p + 3]) bs[p + 4]) (p + 5) (p + 6) (by omega) (by omega)]
  simp only [Nat.reduceAdd]
  refine reach_step (stepM hrun (f_7b8 hP hCL)) ?_
  by_cases hk5 : r = 6
  · simp only [ex_bCond, mkS_pstate, mkS_pc, cond_EQ, hr2, mkS_setPC, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, hk5, decide_true, if_true, show (6 : ℕ) < 2 ^ 64 by norm_num]
    rw [cb_end _ (by omega)]
    refine epi hP hCL hrun hE.hal hE.hF hE.hS _ ?_; rfl
  simp only [ex_bCond, mkS_pstate, mkS_pc, cond_EQ, hr2, mkS_setPC, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, hk5, decide_false, Bool.false_eq_true, if_false, show (6 : ℕ) < 2 ^ 64 by norm_num]
  -- byte 6
  obtain ⟨cr6, rb6⟩ := ro_read8 hE.hbuf (p + 6) (by omega)
  rw [BitVec.ofNat_add] at cr6 rb6
  refine reach_step (stepM hrun (f_7bc hP hCL)) ?_
  simp only [ex_ldr, execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode,
      rd_x1, BitVec.add_zero, MemWidth.bytes, Memory.readSized, Bool.not_true, Bool.false_eq_true,
      if_false, ite_false, State.writeReg, wr_x8, wr_x9, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd,
      mkS_mem, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, sw8, cr6, rb6]
  refine roundT hE hCL 1996 (f_7c0 hP hCL) (f_7c4 hP hCL) (f_7c8 hP hCL) (f_7cc hP hCL) bs[p + 6] (tstep (tstep (tstep (tstep (tstep (tstep c bs[p]) bs[p + 1]) bs[p + 2]) bs[p + 3]) bs[p + 4]) bs[p + 5]) rfl rfl rfl (fun v => ?_)
  rw [cb_step (tstep (tstep (tstep (tstep (tstep (tstep c bs[p]) bs[p + 1]) bs[p + 2]) bs[p + 3]) bs[p + 4]) bs[p + 5]) (p + 6) (p + 7) (by omega) (by omega)]
  simp only [Nat.reduceAdd]
  rw [cb_end _ (by omega)]
  refine epi hP hCL hrun hE.hal hE.hF hE.hS _ ?_; rfl

end

end ZlibCrc32.Crcz.PartT
end

open Arm64 Arm64.Obj
open ZlibCrc32 ZlibCrc32.Crcz in
theorem solution {pl : Placement} {s0 : State} {bs : List (BitVec 8)} {m : Memory}
    {ps : PState} {R : Regs} (hE : Env pl s0 bs m) (c : BitVec 32) (p r : ℕ)
    (hpr : p + r = bs.length) (hr1 : 1 ≤ r) (hr7 : r ≤ 7)
    (h1 : R.x1 = s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 p) (h2 : R.x2 = BitVec.ofNat 64 r)
    (h9 : R.x9 = c.setWidth 64) (h13 : R.x13 = pl.ρ crcTabSym) :
    Reach pl s0 ((~~~ crcBytes c (bs.drop p)).setWidth 64)
      (mkS s0 m (spIn s0) (pl.base + 1824#64) ps R) :=

  ZlibCrc32.Crcz.PartT.tail hE c p r hpr hr1 hr7 h1 h2 h9 h13
