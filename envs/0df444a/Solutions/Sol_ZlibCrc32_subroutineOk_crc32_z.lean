-- Prove2me | solution 1 for ZlibCrc32.subroutineOk_crc32_z
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T13:26:04.261823+00:00
-- url     : https://prove2.me/submissions/2a06b701-ecf4-4bd6-9ade-29b2bb1a25a7

import Mathlib.Tactic.IntervalCases
import Definitions.Def_ZlibCrc32_CrczModel
import Mathlib.Data.List.GetD
import Theorems.Thm_ZlibCrc32_crc32_z_adrp_pairs
import Theorems.Thm_ZlibCrc32_Crcz_reach_tail
import Theorems.Thm_ZlibCrc32_Crcz_reach_loop8
import Theorems.Thm_ZlibCrc32_Crcz_holds32_crcBytes
import Theorems.Thm_ZlibCrc32_Crcz_holds32_braidedResult

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

theorem f_000 : (prog pl).fetchMem m (pl.base + 12#64) = some (Instr.cbz (RegWidth.W64) false (Reg.gpr 0x01#5) 0x0000000000000040#64) :=
  fetch_at hP hCL 0 0 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_004 : (prog pl).fetchMem m (pl.base + 16#64) = some (Instr.str (MemWidth.X64) (Reg.gpr 0x1e#5) (AddrMode.PreIndex (Reg.sp) 0xffffffffffffffa0#64)) :=
  fetch_at hP hCL 0 1 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_008 : (prog pl).fetchMem m (pl.base + 20#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x02#5) 0x02f#12 false) :=
  fetch_at hP hCL 0 2 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_00c : (prog pl).fetchMem m (pl.base + 24#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.ORN) (Reg.gpr 0x09#5) (Reg.xzr) (Reg.gpr 0x00#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 0 3 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_018 : (prog pl).fetchMem m (pl.base + 36#64) = some (Instr.stp (RegWidth.W64) (Reg.gpr 0x1c#5) (Reg.gpr 0x1b#5) (AddrMode.Offset (Reg.sp) 0x0000000000000010#64)) :=
  fetch_at hP hCL 0 6 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_01c : (prog pl).fetchMem m (pl.base + 40#64) = some (Instr.stp (RegWidth.W64) (Reg.gpr 0x1a#5) (Reg.gpr 0x19#5) (AddrMode.Offset (Reg.sp) 0x0000000000000020#64)) :=
  fetch_at hP hCL 0 7 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_020 : (prog pl).fetchMem m (pl.base + 44#64) = some (Instr.stp (RegWidth.W64) (Reg.gpr 0x18#5) (Reg.gpr 0x17#5) (AddrMode.Offset (Reg.sp) 0x0000000000000030#64)) :=
  fetch_at hP hCL 0 8 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_024 : (prog pl).fetchMem m (pl.base + 48#64) = some (Instr.stp (RegWidth.W64) (Reg.gpr 0x16#5) (Reg.gpr 0x15#5) (AddrMode.Offset (Reg.sp) 0x0000000000000040#64)) :=
  fetch_at hP hCL 0 9 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_028 : (prog pl).fetchMem m (pl.base + 52#64) = some (Instr.stp (RegWidth.W64) (Reg.gpr 0x14#5) (Reg.gpr 0x13#5) (AddrMode.Offset (Reg.sp) 0x0000000000000050#64)) :=
  fetch_at hP hCL 0 10 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_02c : (prog pl).fetchMem m (pl.base + 56#64) = some (Instr.bCond (CondCode.CS) 0x000000000000001c#64) :=
  fetch_at hP hCL 0 11 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_030 : (prog pl).fetchMem m (pl.base + 60#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x02#5) 0x008#12 false) :=
  fetch_at hP hCL 0 12 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_034 : (prog pl).fetchMem m (pl.base + 64#64) = some (Instr.bCond (CondCode.CS) 0x0000000000000624#64) :=
  fetch_at hP hCL 0 13 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_038 : (prog pl).fetchMem m (pl.base + 68#64) = some (Instr.cbz (RegWidth.W64) true (Reg.gpr 0x02#5) 0x00000000000006dc#64) :=
  fetch_at hP hCL 0 14 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_03c : (prog pl).fetchMem m (pl.base + 72#64) = some (Instr.b 0x0000000000000794#64) :=
  fetch_at hP hCL 0 15 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_040 : (prog pl).fetchMem m (pl.base + 76#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x00#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 0 16 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_044 : (prog pl).fetchMem m (pl.base + 80#64) = some (Instr.ret (Reg.gpr 0x1e#5)) :=
  fetch_at hP hCL 0 17 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_048 : (prog pl).fetchMem m (pl.base + 84#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.ANDS) (Reg.xzr) (Reg.gpr 0x01#5) 0x0000000000000007#64) :=
  fetch_at hP hCL 0 18 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_04c : (prog pl).fetchMem m (pl.base + 88#64) = some (Instr.bCond (CondCode.EQ) 0x0000000000000150#64) :=
  fetch_at hP hCL 0 19 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_050 : (prog pl).fetchMem m (pl.base + 92#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0a#5) (Reg.xzr) (Reg.gpr 0x01#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 0 20 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_054 : (prog pl).fetchMem m (pl.base + 96#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x0b#5) (AddrMode.PostIndex (Reg.gpr 0x0a#5) 0x0000000000000001#64)) :=
  fetch_at hP hCL 0 21 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_058 : (prog pl).fetchMem m (pl.base + 100#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x0b#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 0 22 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_05c : (prog pl).fetchMem m (pl.base + 104#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0b#5) (Reg.gpr 0x0b#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 0 23 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_060 : (prog pl).fetchMem m (pl.base + 108#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0c#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x0b#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 0 24 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_064 : (prog pl).fetchMem m (pl.base + 112#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.gpr 0x0b#5) (Reg.gpr 0x02#5) 0x001#12 false) :=
  fetch_at hP hCL 0 25 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_068 : (prog pl).fetchMem m (pl.base + 116#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 0 26 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_06c : (prog pl).fetchMem m (pl.base + 120#64) = some (Instr.bCond (CondCode.EQ) 0x000000000000011c#64) :=
  fetch_at hP hCL 0 27 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_070 : (prog pl).fetchMem m (pl.base + 124#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0c#5) (Reg.gpr 0x0a#5) 0x0000000000000007#64) :=
  fetch_at hP hCL 0 28 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_074 : (prog pl).fetchMem m (pl.base + 128#64) = some (Instr.cbz (RegWidth.W64) false (Reg.gpr 0x0c#5) 0x0000000000000114#64) :=
  fetch_at hP hCL 0 29 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_078 : (prog pl).fetchMem m (pl.base + 132#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000001#64)) :=
  fetch_at hP hCL 0 30 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_07c : (prog pl).fetchMem m (pl.base + 136#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 0 31 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_080 : (prog pl).fetchMem m (pl.base + 140#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 1 0 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_084 : (prog pl).fetchMem m (pl.base + 144#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0b#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 1 1 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_088 : (prog pl).fetchMem m (pl.base + 148#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.gpr 0x0a#5) (Reg.gpr 0x02#5) 0x002#12 false) :=
  fetch_at hP hCL 1 2 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_08c : (prog pl).fetchMem m (pl.base + 152#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 1 3 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_090 : (prog pl).fetchMem m (pl.base + 156#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0b#5) (Reg.gpr 0x01#5) 0x002#12 false) :=
  fetch_at hP hCL 1 4 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_094 : (prog pl).fetchMem m (pl.base + 160#64) = some (Instr.bCond (CondCode.EQ) 0x0000000000000100#64) :=
  fetch_at hP hCL 1 5 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_098 : (prog pl).fetchMem m (pl.base + 164#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0c#5) (Reg.gpr 0x0b#5) 0x0000000000000007#64) :=
  fetch_at hP hCL 1 6 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_09c : (prog pl).fetchMem m (pl.base + 168#64) = some (Instr.cbz (RegWidth.W64) false (Reg.gpr 0x0c#5) 0x00000000000000f8#64) :=
  fetch_at hP hCL 1 7 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0a0 : (prog pl).fetchMem m (pl.base + 172#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000002#64)) :=
  fetch_at hP hCL 1 8 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0a4 : (prog pl).fetchMem m (pl.base + 176#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 1 9 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0a8 : (prog pl).fetchMem m (pl.base + 180#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 1 10 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0ac : (prog pl).fetchMem m (pl.base + 184#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0b#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 1 11 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0b0 : (prog pl).fetchMem m (pl.base + 188#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.gpr 0x0a#5) (Reg.gpr 0x02#5) 0x003#12 false) :=
  fetch_at hP hCL 1 12 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0b4 : (prog pl).fetchMem m (pl.base + 192#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 1 13 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0b8 : (prog pl).fetchMem m (pl.base + 196#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0b#5) (Reg.gpr 0x01#5) 0x003#12 false) :=
  fetch_at hP hCL 1 14 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0bc : (prog pl).fetchMem m (pl.base + 200#64) = some (Instr.bCond (CondCode.EQ) 0x00000000000000d8#64) :=
  fetch_at hP hCL 1 15 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0c0 : (prog pl).fetchMem m (pl.base + 204#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0c#5) (Reg.gpr 0x0b#5) 0x0000000000000007#64) :=
  fetch_at hP hCL 1 16 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0c4 : (prog pl).fetchMem m (pl.base + 208#64) = some (Instr.cbz (RegWidth.W64) false (Reg.gpr 0x0c#5) 0x00000000000000d0#64) :=
  fetch_at hP hCL 1 17 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0c8 : (prog pl).fetchMem m (pl.base + 212#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000003#64)) :=
  fetch_at hP hCL 1 18 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0cc : (prog pl).fetchMem m (pl.base + 216#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 1 19 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0d0 : (prog pl).fetchMem m (pl.base + 220#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 1 20 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0d4 : (prog pl).fetchMem m (pl.base + 224#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0b#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 1 21 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0d8 : (prog pl).fetchMem m (pl.base + 228#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.gpr 0x0a#5) (Reg.gpr 0x02#5) 0x004#12 false) :=
  fetch_at hP hCL 1 22 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0dc : (prog pl).fetchMem m (pl.base + 232#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 1 23 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0e0 : (prog pl).fetchMem m (pl.base + 236#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0b#5) (Reg.gpr 0x01#5) 0x004#12 false) :=
  fetch_at hP hCL 1 24 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0e4 : (prog pl).fetchMem m (pl.base + 240#64) = some (Instr.bCond (CondCode.EQ) 0x00000000000000b0#64) :=
  fetch_at hP hCL 1 25 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0e8 : (prog pl).fetchMem m (pl.base + 244#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0c#5) (Reg.gpr 0x0b#5) 0x0000000000000007#64) :=
  fetch_at hP hCL 1 26 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0ec : (prog pl).fetchMem m (pl.base + 248#64) = some (Instr.cbz (RegWidth.W64) false (Reg.gpr 0x0c#5) 0x00000000000000a8#64) :=
  fetch_at hP hCL 1 27 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0f0 : (prog pl).fetchMem m (pl.base + 252#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000004#64)) :=
  fetch_at hP hCL 1 28 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0f4 : (prog pl).fetchMem m (pl.base + 256#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 1 29 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0f8 : (prog pl).fetchMem m (pl.base + 260#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 1 30 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_0fc : (prog pl).fetchMem m (pl.base + 264#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0b#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 1 31 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_100 : (prog pl).fetchMem m (pl.base + 268#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.gpr 0x0a#5) (Reg.gpr 0x02#5) 0x005#12 false) :=
  fetch_at hP hCL 2 0 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_104 : (prog pl).fetchMem m (pl.base + 272#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 2 1 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_108 : (prog pl).fetchMem m (pl.base + 276#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0b#5) (Reg.gpr 0x01#5) 0x005#12 false) :=
  fetch_at hP hCL 2 2 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_10c : (prog pl).fetchMem m (pl.base + 280#64) = some (Instr.bCond (CondCode.EQ) 0x0000000000000088#64) :=
  fetch_at hP hCL 2 3 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_110 : (prog pl).fetchMem m (pl.base + 284#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0c#5) (Reg.gpr 0x0b#5) 0x0000000000000007#64) :=
  fetch_at hP hCL 2 4 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_114 : (prog pl).fetchMem m (pl.base + 288#64) = some (Instr.cbz (RegWidth.W64) false (Reg.gpr 0x0c#5) 0x0000000000000080#64) :=
  fetch_at hP hCL 2 5 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_118 : (prog pl).fetchMem m (pl.base + 292#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000005#64)) :=
  fetch_at hP hCL 2 6 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_11c : (prog pl).fetchMem m (pl.base + 296#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 2 7 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_120 : (prog pl).fetchMem m (pl.base + 300#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 2 8 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_124 : (prog pl).fetchMem m (pl.base + 304#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0b#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 2 9 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_128 : (prog pl).fetchMem m (pl.base + 308#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.gpr 0x0a#5) (Reg.gpr 0x02#5) 0x006#12 false) :=
  fetch_at hP hCL 2 10 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_12c : (prog pl).fetchMem m (pl.base + 312#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 2 11 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_130 : (prog pl).fetchMem m (pl.base + 316#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0b#5) (Reg.gpr 0x01#5) 0x006#12 false) :=
  fetch_at hP hCL 2 12 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_134 : (prog pl).fetchMem m (pl.base + 320#64) = some (Instr.bCond (CondCode.EQ) 0x0000000000000060#64) :=
  fetch_at hP hCL 2 13 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_138 : (prog pl).fetchMem m (pl.base + 324#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0c#5) (Reg.gpr 0x0b#5) 0x0000000000000007#64) :=
  fetch_at hP hCL 2 14 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_13c : (prog pl).fetchMem m (pl.base + 328#64) = some (Instr.cbz (RegWidth.W64) false (Reg.gpr 0x0c#5) 0x0000000000000058#64) :=
  fetch_at hP hCL 2 15 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_140 : (prog pl).fetchMem m (pl.base + 332#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.B8) false (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000006#64)) :=
  fetch_at hP hCL 2 16 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_144 : (prog pl).fetchMem m (pl.base + 336#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 2 17 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_148 : (prog pl).fetchMem m (pl.base + 340#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 2 18 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_14c : (prog pl).fetchMem m (pl.base + 344#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0b#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 2 19 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_150 : (prog pl).fetchMem m (pl.base + 348#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.gpr 0x0a#5) (Reg.gpr 0x02#5) 0x007#12 false) :=
  fetch_at hP hCL 2 20 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_154 : (prog pl).fetchMem m (pl.base + 352#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x09#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 2 21 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_158 : (prog pl).fetchMem m (pl.base + 356#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0b#5) (Reg.gpr 0x01#5) 0x007#12 false) :=
  fetch_at hP hCL 2 22 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_15c : (prog pl).fetchMem m (pl.base + 360#64) = some (Instr.bCond (CondCode.EQ) 0x0000000000000038#64) :=
  fetch_at hP hCL 2 23 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_160 : (prog pl).fetchMem m (pl.base + 364#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0c#5) (Reg.gpr 0x0b#5) 0x0000000000000007#64) :=
  fetch_at hP hCL 2 24 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_164 : (prog pl).fetchMem m (pl.base + 368#64) = some (Instr.cbz (RegWidth.W64) false (Reg.gpr 0x0c#5) 0x0000000000000030#64) :=
  fetch_at hP hCL 2 25 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_188 : (prog pl).fetchMem m (pl.base + 404#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x02#5) (Reg.xzr) (Reg.gpr 0x0b#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 3 2 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_18c : (prog pl).fetchMem m (pl.base + 408#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x01#5) (Reg.xzr) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 3 3 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_190 : (prog pl).fetchMem m (pl.base + 412#64) = some (Instr.b 0x000000000000000c#64) :=
  fetch_at hP hCL 3 4 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_194 : (prog pl).fetchMem m (pl.base + 416#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x02#5) (Reg.xzr) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 3 5 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_198 : (prog pl).fetchMem m (pl.base + 420#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x01#5) (Reg.xzr) (Reg.gpr 0x0b#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 3 6 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_19c : (prog pl).fetchMem m (pl.base + 424#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0a#5) (Reg.xzr) 0xcccccccccccccccc#64) :=
  fetch_at hP hCL 3 7 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1a0 : (prog pl).fetchMem m (pl.base + 428#64) = some (Instr.moveWide (RegWidth.W64) (MoveWideOp.MOVN) (Reg.gpr 0x0b#5) 0x0027#16 0) :=
  fetch_at hP hCL 3 8 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1a4 : (prog pl).fetchMem m (pl.base + 432#64) = some (Instr.moveWide (RegWidth.W64) (MoveWideOp.MOVK) (Reg.gpr 0x0a#5) 0xcccd#16 0) :=
  fetch_at hP hCL 3 9 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1a8 : (prog pl).fetchMem m (pl.base + 436#64) = some (Instr.dataProc3 (RegWidth.W64) (DataProc3Op.UMULH) (Reg.gpr 0x0a#5) (Reg.gpr 0x02#5) (Reg.gpr 0x0a#5) (Reg.xzr)) :=
  fetch_at hP hCL 3 10 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1ac : (prog pl).fetchMem m (pl.base + 440#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) 5 63) :=
  fetch_at hP hCL 3 11 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1b0 : (prog pl).fetchMem m (pl.base + 444#64) = some (Instr.dataProc3 (RegWidth.W64) (DataProc3Op.MADD) (Reg.gpr 0x02#5) (Reg.gpr 0x08#5) (Reg.gpr 0x0b#5) (Reg.gpr 0x02#5)) :=
  fetch_at hP hCL 3 12 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1b4 : (prog pl).fetchMem m (pl.base + 448#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.gpr 0x0b#5) (Reg.gpr 0x08#5) 0x001#12 false) :=
  fetch_at hP hCL 3 13 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1b8 : (prog pl).fetchMem m (pl.base + 452#64) = some (Instr.bCond (CondCode.EQ) 0x0000000000000260#64) :=
  fetch_at hP hCL 3 14 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1c4 : (prog pl).fetchMem m (pl.base + 464#64) = some (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x0d#5) 0x1400#16 0) :=
  fetch_at hP hCL 3 17 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1c8 : (prog pl).fetchMem m (pl.base + 468#64) = some (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x0f#5) 0x1800#16 0) :=
  fetch_at hP hCL 3 18 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1cc : (prog pl).fetchMem m (pl.base + 472#64) = some (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x10#5) 0x1c00#16 0) :=
  fetch_at hP hCL 3 19 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1d0 : (prog pl).fetchMem m (pl.base + 476#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0e#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 3 20 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1d4 : (prog pl).fetchMem m (pl.base + 480#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x12#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 3 21 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1d8 : (prog pl).fetchMem m (pl.base + 484#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x13#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 3 22 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1dc : (prog pl).fetchMem m (pl.base + 488#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x00#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 3 23 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1e0 : (prog pl).fetchMem m (pl.base + 492#64) = some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0d#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x0d#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 3 24 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1e4 : (prog pl).fetchMem m (pl.base + 496#64) = some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x0f#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x0f#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 3 25 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1e8 : (prog pl).fetchMem m (pl.base + 500#64) = some (Instr.addSubShift (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x10#5) (Reg.gpr 0x0c#5) (Reg.gpr 0x10#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 3 26 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1ec : (prog pl).fetchMem m (pl.base + 504#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x11#5) (Reg.xzr) (Reg.gpr 0x01#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 3 27 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1f0 : (prog pl).fetchMem m (pl.base + 508#64) = some (Instr.str (MemWidth.X64) (Reg.gpr 0x08#5) (AddrMode.Offset (Reg.sp) 0x0000000000000008#64)) :=
  fetch_at hP hCL 3 28 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1f4 : (prog pl).fetchMem m (pl.base + 512#64) = some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x05#5) (Reg.gpr 0x04#5) (AddrMode.Offset (Reg.gpr 0x11#5) 0x0000000000000010#64)) :=
  fetch_at hP hCL 3 29 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1f8 : (prog pl).fetchMem m (pl.base + 516#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x19#5) (Reg.gpr 0x0c#5) 0x400#12 false) :=
  fetch_at hP hCL 3 30 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_1fc : (prog pl).fetchMem m (pl.base + 520#64) = some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x07#5) (Reg.gpr 0x06#5) (AddrMode.Offset (Reg.gpr 0x11#5) 0x0000000000000000#64)) :=
  fetch_at hP hCL 3 31 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_200 : (prog pl).fetchMem m (pl.base + 524#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x08#5) (Reg.gpr 0x0c#5) 0xc00#12 false) :=
  fetch_at hP hCL 4 0 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_204 : (prog pl).fetchMem m (pl.base + 528#64) = some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x03#5) (AddrMode.Offset (Reg.gpr 0x11#5) 0x0000000000000020#64)) :=
  fetch_at hP hCL 4 1 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_208 : (prog pl).fetchMem m (pl.base + 532#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.gpr 0x0b#5) (Reg.gpr 0x0b#5) 0x001#12 false) :=
  fetch_at hP hCL 4 2 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_20c : (prog pl).fetchMem m (pl.base + 536#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x11#5) (Reg.gpr 0x11#5) 0x028#12 false) :=
  fetch_at hP hCL 4 3 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_210 : (prog pl).fetchMem m (pl.base + 540#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x16#5) (Reg.gpr 0x05#5) (Reg.gpr 0x00#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 4 4 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_214 : (prog pl).fetchMem m (pl.base + 544#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x15#5) (Reg.gpr 0x04#5) (Reg.gpr 0x12#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 4 5 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_218 : (prog pl).fetchMem m (pl.base + 548#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x18#5) (Reg.gpr 0x07#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 4 6 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_21c : (prog pl).fetchMem m (pl.base + 552#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x17#5) (Reg.gpr 0x06#5) (Reg.gpr 0x13#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 4 7 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_220 : (prog pl).fetchMem m (pl.base + 556#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x00#5) (Reg.gpr 0x16#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 4 8 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_224 : (prog pl).fetchMem m (pl.base + 560#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x13#5) (AddrMode.RegOffset (Reg.gpr 0x0c#5) (Reg.gpr 0x00#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 4 9 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_228 : (prog pl).fetchMem m (pl.base + 564#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x00#5) (Reg.gpr 0x18#5) 8 15) :=
  fetch_at hP hCL 4 10 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_22c : (prog pl).fetchMem m (pl.base + 568#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x1a#5) (Reg.gpr 0x17#5) 8 15) :=
  fetch_at hP hCL 4 11 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_230 : (prog pl).fetchMem m (pl.base + 572#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x03#5) (Reg.gpr 0x0e#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 4 12 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_234 : (prog pl).fetchMem m (pl.base + 576#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0e#5) (Reg.gpr 0x18#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 4 13 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_238 : (prog pl).fetchMem m (pl.base + 580#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x12#5) (Reg.gpr 0x17#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 4 14 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_23c : (prog pl).fetchMem m (pl.base + 584#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0e#5) (AddrMode.RegOffset (Reg.gpr 0x0c#5) (Reg.gpr 0x0e#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 4 15 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_240 : (prog pl).fetchMem m (pl.base + 588#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x12#5) (AddrMode.RegOffset (Reg.gpr 0x0c#5) (Reg.gpr 0x12#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 4 16 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_244 : (prog pl).fetchMem m (pl.base + 592#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x00#5) (AddrMode.RegOffset (Reg.gpr 0x19#5) (Reg.gpr 0x00#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 4 17 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_248 : (prog pl).fetchMem m (pl.base + 596#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x1a#5) (AddrMode.RegOffset (Reg.gpr 0x19#5) (Reg.gpr 0x1a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 4 18 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_24c : (prog pl).fetchMem m (pl.base + 600#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x1c#5) (Reg.gpr 0x16#5) 8 15) :=
  fetch_at hP hCL 4 19 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_250 : (prog pl).fetchMem m (pl.base + 604#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x1e#5) (Reg.gpr 0x15#5) 8 15) :=
  fetch_at hP hCL 4 20 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_254 : (prog pl).fetchMem m (pl.base + 608#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0a#5) (Reg.gpr 0x09#5) 8 15) :=
  fetch_at hP hCL 4 21 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_258 : (prog pl).fetchMem m (pl.base + 612#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x14#5) (Reg.gpr 0x15#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 4 22 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_25c : (prog pl).fetchMem m (pl.base + 616#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x1b#5) (Reg.gpr 0x09#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 4 23 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_260 : (prog pl).fetchMem m (pl.base + 620#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x14#5) (AddrMode.RegOffset (Reg.gpr 0x0c#5) (Reg.gpr 0x14#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 4 24 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_264 : (prog pl).fetchMem m (pl.base + 624#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x1b#5) (AddrMode.RegOffset (Reg.gpr 0x0c#5) (Reg.gpr 0x1b#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 4 25 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_268 : (prog pl).fetchMem m (pl.base + 628#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x0e#5) (Reg.gpr 0x00#5) (Reg.gpr 0x0e#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 4 26 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_26c : (prog pl).fetchMem m (pl.base + 632#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x00#5) (Reg.gpr 0x1a#5) (Reg.gpr 0x12#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 4 27 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_270 : (prog pl).fetchMem m (pl.base + 636#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x12#5) (AddrMode.RegOffset (Reg.gpr 0x19#5) (Reg.gpr 0x1c#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 4 28 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_274 : (prog pl).fetchMem m (pl.base + 640#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x1a#5) (AddrMode.RegOffset (Reg.gpr 0x19#5) (Reg.gpr 0x1e#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 4 29 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_278 : (prog pl).fetchMem m (pl.base + 644#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0a#5) (AddrMode.RegOffset (Reg.gpr 0x19#5) (Reg.gpr 0x0a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 4 30 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_27c : (prog pl).fetchMem m (pl.base + 648#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x19#5) (Reg.gpr 0x18#5) 16 23) :=
  fetch_at hP hCL 4 31 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_280 : (prog pl).fetchMem m (pl.base + 652#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x1c#5) (Reg.gpr 0x17#5) 16 23) :=
  fetch_at hP hCL 5 0 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_284 : (prog pl).fetchMem m (pl.base + 656#64) = some (Instr.bitfield (RegWidth.W32) (BitfieldOp.UBFM) (Reg.gpr 0x18#5) (Reg.gpr 0x18#5) 24 31) :=
  fetch_at hP hCL 5 1 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_288 : (prog pl).fetchMem m (pl.base + 660#64) = some (Instr.bitfield (RegWidth.W32) (BitfieldOp.UBFM) (Reg.gpr 0x17#5) (Reg.gpr 0x17#5) 24 31) :=
  fetch_at hP hCL 5 2 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_28c : (prog pl).fetchMem m (pl.base + 664#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x13#5) (Reg.gpr 0x12#5) (Reg.gpr 0x13#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 5 3 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_290 : (prog pl).fetchMem m (pl.base + 668#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x14#5) (Reg.gpr 0x1a#5) (Reg.gpr 0x14#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 5 4 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_294 : (prog pl).fetchMem m (pl.base + 672#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x1a#5) (Reg.gpr 0x0c#5) 0x800#12 false) :=
  fetch_at hP hCL 5 5 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_298 : (prog pl).fetchMem m (pl.base + 676#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x12#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x1b#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 5 6 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_29c : (prog pl).fetchMem m (pl.base + 680#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x1b#5) (Reg.gpr 0x16#5) 16 23) :=
  fetch_at hP hCL 5 7 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2a0 : (prog pl).fetchMem m (pl.base + 684#64) = some (Instr.bitfield (RegWidth.W32) (BitfieldOp.UBFM) (Reg.gpr 0x16#5) (Reg.gpr 0x16#5) 24 31) :=
  fetch_at hP hCL 5 8 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2a4 : (prog pl).fetchMem m (pl.base + 688#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0a#5) (AddrMode.RegOffset (Reg.gpr 0x1a#5) (Reg.gpr 0x19#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 5 9 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2a8 : (prog pl).fetchMem m (pl.base + 692#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x19#5) (AddrMode.RegOffset (Reg.gpr 0x1a#5) (Reg.gpr 0x1c#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 5 10 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2ac : (prog pl).fetchMem m (pl.base + 696#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x1c#5) (Reg.gpr 0x15#5) 16 23) :=
  fetch_at hP hCL 5 11 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2b0 : (prog pl).fetchMem m (pl.base + 700#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x18#5) (AddrMode.RegOffset (Reg.gpr 0x08#5) (Reg.gpr 0x18#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 5 12 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2b4 : (prog pl).fetchMem m (pl.base + 704#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x17#5) (AddrMode.RegOffset (Reg.gpr 0x08#5) (Reg.gpr 0x17#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 5 13 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2b8 : (prog pl).fetchMem m (pl.base + 708#64) = some (Instr.bitfield (RegWidth.W32) (BitfieldOp.UBFM) (Reg.gpr 0x15#5) (Reg.gpr 0x15#5) 24 31) :=
  fetch_at hP hCL 5 14 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2bc : (prog pl).fetchMem m (pl.base + 712#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x1b#5) (AddrMode.RegOffset (Reg.gpr 0x1a#5) (Reg.gpr 0x1b#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 5 15 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2c0 : (prog pl).fetchMem m (pl.base + 716#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x16#5) (AddrMode.RegOffset (Reg.gpr 0x08#5) (Reg.gpr 0x16#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 5 16 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2c4 : (prog pl).fetchMem m (pl.base + 720#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x1c#5) (AddrMode.RegOffset (Reg.gpr 0x1a#5) (Reg.gpr 0x1c#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 5 17 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2c8 : (prog pl).fetchMem m (pl.base + 724#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x0a#5) (Reg.gpr 0x18#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 5 18 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2cc : (prog pl).fetchMem m (pl.base + 728#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x17#5) (Reg.gpr 0x17#5) (Reg.gpr 0x19#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 5 19 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2d0 : (prog pl).fetchMem m (pl.base + 732#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x18#5) (Reg.gpr 0x07#5) 32 39) :=
  fetch_at hP hCL 5 20 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2d4 : (prog pl).fetchMem m (pl.base + 736#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x19#5) (Reg.gpr 0x06#5) 32 39) :=
  fetch_at hP hCL 5 21 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2d8 : (prog pl).fetchMem m (pl.base + 740#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x15#5) (AddrMode.RegOffset (Reg.gpr 0x08#5) (Reg.gpr 0x15#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 5 22 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2dc : (prog pl).fetchMem m (pl.base + 744#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x16#5) (Reg.gpr 0x16#5) (Reg.gpr 0x1b#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 5 23 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2e0 : (prog pl).fetchMem m (pl.base + 748#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x1b#5) (Reg.gpr 0x0c#5) 0x001#12 true) :=
  fetch_at hP hCL 5 24 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2e4 : (prog pl).fetchMem m (pl.base + 752#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x1e#5) (Reg.gpr 0x09#5) 16 23) :=
  fetch_at hP hCL 5 25 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2e8 : (prog pl).fetchMem m (pl.base + 756#64) = some (Instr.bitfield (RegWidth.W32) (BitfieldOp.UBFM) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) 24 31) :=
  fetch_at hP hCL 5 26 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2ec : (prog pl).fetchMem m (pl.base + 760#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x18#5) (AddrMode.RegOffset (Reg.gpr 0x1b#5) (Reg.gpr 0x18#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 5 27 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2f0 : (prog pl).fetchMem m (pl.base + 764#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x19#5) (AddrMode.RegOffset (Reg.gpr 0x1b#5) (Reg.gpr 0x19#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 5 28 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2f4 : (prog pl).fetchMem m (pl.base + 768#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x15#5) (Reg.gpr 0x15#5) (Reg.gpr 0x1c#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 5 29 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2f8 : (prog pl).fetchMem m (pl.base + 772#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x1c#5) (Reg.gpr 0x05#5) 32 39) :=
  fetch_at hP hCL 5 30 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_2fc : (prog pl).fetchMem m (pl.base + 776#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x1a#5) (AddrMode.RegOffset (Reg.gpr 0x1a#5) (Reg.gpr 0x1e#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 5 31 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_300 : (prog pl).fetchMem m (pl.base + 780#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x1e#5) (Reg.gpr 0x04#5) 32 39) :=
  fetch_at hP hCL 6 0 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_304 : (prog pl).fetchMem m (pl.base + 784#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x08#5) (AddrMode.RegOffset (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 6 1 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_308 : (prog pl).fetchMem m (pl.base + 788#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x18#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 6 2 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_30c : (prog pl).fetchMem m (pl.base + 792#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x0a#5) (Reg.gpr 0x19#5) (Reg.gpr 0x17#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 6 3 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_310 : (prog pl).fetchMem m (pl.base + 796#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x17#5) (AddrMode.RegOffset (Reg.gpr 0x1b#5) (Reg.gpr 0x1c#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 6 4 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_314 : (prog pl).fetchMem m (pl.base + 800#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x19#5) (Reg.gpr 0x03#5) 32 39) :=
  fetch_at hP hCL 6 5 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_318 : (prog pl).fetchMem m (pl.base + 804#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x18#5) (AddrMode.RegOffset (Reg.gpr 0x1b#5) (Reg.gpr 0x1e#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 6 6 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_31c : (prog pl).fetchMem m (pl.base + 808#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x00#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x00#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 6 7 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_320 : (prog pl).fetchMem m (pl.base + 812#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x0a#5) (Reg.gpr 0x17#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 6 8 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_324 : (prog pl).fetchMem m (pl.base + 816#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x1a#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 6 9 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_328 : (prog pl).fetchMem m (pl.base + 820#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) (Reg.gpr 0x0e#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 6 10 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_32c : (prog pl).fetchMem m (pl.base + 824#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x16#5) (AddrMode.RegOffset (Reg.gpr 0x1b#5) (Reg.gpr 0x19#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 6 11 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_330 : (prog pl).fetchMem m (pl.base + 828#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x0e#5) (Reg.gpr 0x18#5) (Reg.gpr 0x15#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 6 12 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_334 : (prog pl).fetchMem m (pl.base + 832#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x15#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x13#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 6 13 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_338 : (prog pl).fetchMem m (pl.base + 836#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0a#5) (Reg.gpr 0x07#5) 40 47) :=
  fetch_at hP hCL 6 14 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_33c : (prog pl).fetchMem m (pl.base + 840#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x13#5) (Reg.gpr 0x06#5) 40 47) :=
  fetch_at hP hCL 6 15 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_340 : (prog pl).fetchMem m (pl.base + 844#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x0e#5) (Reg.gpr 0x0e#5) (Reg.gpr 0x14#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 6 16 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_344 : (prog pl).fetchMem m (pl.base + 848#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x16#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 6 17 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_348 : (prog pl).fetchMem m (pl.base + 852#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x16#5) (Reg.gpr 0x05#5) 40 47) :=
  fetch_at hP hCL 6 18 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_34c : (prog pl).fetchMem m (pl.base + 856#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x19#5) (Reg.gpr 0x05#5) 48 55) :=
  fetch_at hP hCL 6 19 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_350 : (prog pl).fetchMem m (pl.base + 860#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x14#5) (Reg.gpr 0x08#5) (Reg.gpr 0x12#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 6 20 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_354 : (prog pl).fetchMem m (pl.base + 864#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x08#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 6 21 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_358 : (prog pl).fetchMem m (pl.base + 868#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x0a#5) (Reg.gpr 0x07#5) 48 55) :=
  fetch_at hP hCL 6 22 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_35c : (prog pl).fetchMem m (pl.base + 872#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x12#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x13#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 6 23 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_360 : (prog pl).fetchMem m (pl.base + 876#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x13#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x16#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 6 24 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_364 : (prog pl).fetchMem m (pl.base + 880#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x16#5) (Reg.gpr 0x06#5) 48 55) :=
  fetch_at hP hCL 6 25 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_368 : (prog pl).fetchMem m (pl.base + 884#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0a#5) (AddrMode.RegOffset (Reg.gpr 0x0f#5) (Reg.gpr 0x0a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 6 26 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_36c : (prog pl).fetchMem m (pl.base + 888#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x17#5) (Reg.gpr 0x04#5) 40 47) :=
  fetch_at hP hCL 6 27 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_370 : (prog pl).fetchMem m (pl.base + 892#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x18#5) (Reg.gpr 0x03#5) 40 47) :=
  fetch_at hP hCL 6 28 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_374 : (prog pl).fetchMem m (pl.base + 896#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x16#5) (AddrMode.RegOffset (Reg.gpr 0x0f#5) (Reg.gpr 0x16#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 6 29 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_378 : (prog pl).fetchMem m (pl.base + 900#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x1a#5) (Reg.gpr 0x04#5) 48 55) :=
  fetch_at hP hCL 6 30 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_37c : (prog pl).fetchMem m (pl.base + 904#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x07#5) (Reg.gpr 0x07#5) 56 63) :=
  fetch_at hP hCL 6 31 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_380 : (prog pl).fetchMem m (pl.base + 908#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 7 0 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_384 : (prog pl).fetchMem m (pl.base + 912#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x06#5) (Reg.gpr 0x06#5) 56 63) :=
  fetch_at hP hCL 7 1 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_388 : (prog pl).fetchMem m (pl.base + 916#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x05#5) (Reg.gpr 0x05#5) 56 63) :=
  fetch_at hP hCL 7 2 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_38c : (prog pl).fetchMem m (pl.base + 920#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x0a#5) (Reg.gpr 0x16#5) (Reg.gpr 0x12#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 7 3 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_390 : (prog pl).fetchMem m (pl.base + 924#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x12#5) (AddrMode.RegOffset (Reg.gpr 0x0f#5) (Reg.gpr 0x19#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 7 4 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_394 : (prog pl).fetchMem m (pl.base + 928#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x19#5) (Reg.gpr 0x03#5) 48 55) :=
  fetch_at hP hCL 7 5 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_398 : (prog pl).fetchMem m (pl.base + 932#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x04#5) (Reg.gpr 0x04#5) 56 63) :=
  fetch_at hP hCL 7 6 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_39c : (prog pl).fetchMem m (pl.base + 936#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x03#5) (Reg.gpr 0x03#5) 56 63) :=
  fetch_at hP hCL 7 7 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3a0 : (prog pl).fetchMem m (pl.base + 940#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x17#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x17#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 7 8 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3a4 : (prog pl).fetchMem m (pl.base + 944#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x18#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x18#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 7 9 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3a8 : (prog pl).fetchMem m (pl.base + 948#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x16#5) (AddrMode.RegOffset (Reg.gpr 0x0f#5) (Reg.gpr 0x1a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 7 10 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3ac : (prog pl).fetchMem m (pl.base + 952#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x12#5) (Reg.gpr 0x12#5) (Reg.gpr 0x13#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 7 11 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3b0 : (prog pl).fetchMem m (pl.base + 956#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x13#5) (AddrMode.RegOffset (Reg.gpr 0x0f#5) (Reg.gpr 0x19#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 7 12 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3b4 : (prog pl).fetchMem m (pl.base + 960#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x07#5) (AddrMode.RegOffset (Reg.gpr 0x10#5) (Reg.gpr 0x07#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 7 13 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3b8 : (prog pl).fetchMem m (pl.base + 964#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x06#5) (AddrMode.RegOffset (Reg.gpr 0x10#5) (Reg.gpr 0x06#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 7 14 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3bc : (prog pl).fetchMem m (pl.base + 968#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x05#5) (AddrMode.RegOffset (Reg.gpr 0x10#5) (Reg.gpr 0x05#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 7 15 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3c0 : (prog pl).fetchMem m (pl.base + 972#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x04#5) (AddrMode.RegOffset (Reg.gpr 0x10#5) (Reg.gpr 0x04#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 7 16 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3c4 : (prog pl).fetchMem m (pl.base + 976#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x03#5) (AddrMode.RegOffset (Reg.gpr 0x10#5) (Reg.gpr 0x03#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 7 17 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3c8 : (prog pl).fetchMem m (pl.base + 980#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x16#5) (Reg.gpr 0x16#5) (Reg.gpr 0x17#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 7 18 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3cc : (prog pl).fetchMem m (pl.base + 984#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x17#5) (Reg.gpr 0x13#5) (Reg.gpr 0x18#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 7 19 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3d0 : (prog pl).fetchMem m (pl.base + 988#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x07#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 7 20 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3d4 : (prog pl).fetchMem m (pl.base + 992#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x0a#5) (Reg.gpr 0x06#5) (Reg.gpr 0x0a#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 7 21 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3d8 : (prog pl).fetchMem m (pl.base + 996#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x12#5) (Reg.gpr 0x05#5) (Reg.gpr 0x12#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 7 22 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3dc : (prog pl).fetchMem m (pl.base + 1000#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 7 23 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3e0 : (prog pl).fetchMem m (pl.base + 1004#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x13#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x00#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 7 24 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3e4 : (prog pl).fetchMem m (pl.base + 1008#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x04#5) (Reg.gpr 0x16#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 7 25 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3e8 : (prog pl).fetchMem m (pl.base + 1012#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x0a#5) (Reg.gpr 0x03#5) (Reg.gpr 0x17#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 7 26 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3ec : (prog pl).fetchMem m (pl.base + 1016#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x00#5) (Reg.gpr 0x12#5) (Reg.gpr 0x15#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 7 27 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3f0 : (prog pl).fetchMem m (pl.base + 1020#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x12#5) (Reg.gpr 0x08#5) (Reg.gpr 0x0e#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 7 28 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3f4 : (prog pl).fetchMem m (pl.base + 1024#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x0e#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x14#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 7 29 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3f8 : (prog pl).fetchMem m (pl.base + 1028#64) = some (Instr.bCond (CondCode.NE) 0xfffffffffffffdfc#64) :=
  fetch_at hP hCL 7 30 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_3fc : (prog pl).fetchMem m (pl.base + 1032#64) = some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.sp) 0x0000000000000008#64)) :=
  fetch_at hP hCL 7 31 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_400 : (prog pl).fetchMem m (pl.base + 1036#64) = some (Instr.moveWide (RegWidth.W32) (MoveWideOp.MOVZ) (Reg.gpr 0x08#5) 0x0028#16 0) :=
  fetch_at hP hCL 8 0 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_40c : (prog pl).fetchMem m (pl.base + 1048#64) = some (Instr.dataProc3 (RegWidth.W64) (DataProc3Op.MADD) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (Reg.gpr 0x01#5)) :=
  fetch_at hP hCL 8 3 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_410 : (prog pl).fetchMem m (pl.base + 1052#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUB) (Reg.gpr 0x01#5) (Reg.gpr 0x08#5) 0x028#12 false) :=
  fetch_at hP hCL 8 4 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_414 : (prog pl).fetchMem m (pl.base + 1056#64) = some (Instr.b 0x0000000000000014#64) :=
  fetch_at hP hCL 8 5 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_418 : (prog pl).fetchMem m (pl.base + 1060#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x00#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 8 6 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_41c : (prog pl).fetchMem m (pl.base + 1064#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x13#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 8 7 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_420 : (prog pl).fetchMem m (pl.base + 1068#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x12#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 8 8 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_424 : (prog pl).fetchMem m (pl.base + 1072#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.ORR) (Reg.gpr 0x0e#5) (Reg.xzr) (Reg.xzr) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 8 9 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_428 : (prog pl).fetchMem m (pl.base + 1076#64) = some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000000#64)) :=
  fetch_at hP hCL 8 10 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_42c : (prog pl).fetchMem m (pl.base + 1080#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 8 11 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_430 : (prog pl).fetchMem m (pl.base + 1084#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 8 12 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_434 : (prog pl).fetchMem m (pl.base + 1088#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 8 13 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_438 : (prog pl).fetchMem m (pl.base + 1092#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 8 14 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_43c : (prog pl).fetchMem m (pl.base + 1096#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 8 15 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_440 : (prog pl).fetchMem m (pl.base + 1100#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 8 16 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_444 : (prog pl).fetchMem m (pl.base + 1104#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 8 17 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_448 : (prog pl).fetchMem m (pl.base + 1108#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 8 18 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_44c : (prog pl).fetchMem m (pl.base + 1112#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 8 19 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_450 : (prog pl).fetchMem m (pl.base + 1116#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 8 20 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_454 : (prog pl).fetchMem m (pl.base + 1120#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 8 21 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_458 : (prog pl).fetchMem m (pl.base + 1124#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 8 22 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_45c : (prog pl).fetchMem m (pl.base + 1128#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 8 23 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_460 : (prog pl).fetchMem m (pl.base + 1132#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 8 24 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_464 : (prog pl).fetchMem m (pl.base + 1136#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 8 25 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_468 : (prog pl).fetchMem m (pl.base + 1140#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 8 26 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_46c : (prog pl).fetchMem m (pl.base + 1144#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 8 27 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_470 : (prog pl).fetchMem m (pl.base + 1148#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 8 28 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_474 : (prog pl).fetchMem m (pl.base + 1152#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 8 29 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_478 : (prog pl).fetchMem m (pl.base + 1156#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 8 30 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_47c : (prog pl).fetchMem m (pl.base + 1160#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 8 31 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_480 : (prog pl).fetchMem m (pl.base + 1164#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 9 0 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_484 : (prog pl).fetchMem m (pl.base + 1168#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 9 1 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_488 : (prog pl).fetchMem m (pl.base + 1172#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 8 63) :=
  fetch_at hP hCL 9 2 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_48c : (prog pl).fetchMem m (pl.base + 1176#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 9 3 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_490 : (prog pl).fetchMem m (pl.base + 1180#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 9 4 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_494 : (prog pl).fetchMem m (pl.base + 1184#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x13#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 9 5 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_498 : (prog pl).fetchMem m (pl.base + 1188#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 9 6 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_49c : (prog pl).fetchMem m (pl.base + 1192#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 9 7 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4a0 : (prog pl).fetchMem m (pl.base + 1196#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 9 8 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4a4 : (prog pl).fetchMem m (pl.base + 1200#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 9 9 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4a8 : (prog pl).fetchMem m (pl.base + 1204#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 9 10 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4ac : (prog pl).fetchMem m (pl.base + 1208#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 9 11 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4b0 : (prog pl).fetchMem m (pl.base + 1212#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 9 12 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4b4 : (prog pl).fetchMem m (pl.base + 1216#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 9 13 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4b8 : (prog pl).fetchMem m (pl.base + 1220#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 9 14 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4bc : (prog pl).fetchMem m (pl.base + 1224#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 9 15 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4c0 : (prog pl).fetchMem m (pl.base + 1228#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 9 16 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4c4 : (prog pl).fetchMem m (pl.base + 1232#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 9 17 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4c8 : (prog pl).fetchMem m (pl.base + 1236#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 9 18 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4cc : (prog pl).fetchMem m (pl.base + 1240#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 9 19 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4d0 : (prog pl).fetchMem m (pl.base + 1244#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 9 20 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4d4 : (prog pl).fetchMem m (pl.base + 1248#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 9 21 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4d8 : (prog pl).fetchMem m (pl.base + 1252#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 9 22 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4dc : (prog pl).fetchMem m (pl.base + 1256#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 9 23 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4e0 : (prog pl).fetchMem m (pl.base + 1260#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 9 24 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4e4 : (prog pl).fetchMem m (pl.base + 1264#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 9 25 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4e8 : (prog pl).fetchMem m (pl.base + 1268#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 9 26 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4ec : (prog pl).fetchMem m (pl.base + 1272#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 9 27 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4f0 : (prog pl).fetchMem m (pl.base + 1276#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 9 28 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4f4 : (prog pl).fetchMem m (pl.base + 1280#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 8 63) :=
  fetch_at hP hCL 9 29 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4f8 : (prog pl).fetchMem m (pl.base + 1284#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 9 30 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_4fc : (prog pl).fetchMem m (pl.base + 1288#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 9 31 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_500 : (prog pl).fetchMem m (pl.base + 1292#64) = some (Instr.ldp (RegWidth.W64) false (Reg.gpr 0x0a#5) (Reg.gpr 0x09#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000010#64)) :=
  fetch_at hP hCL 10 0 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_504 : (prog pl).fetchMem m (pl.base + 1296#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x0a#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x00#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 10 1 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_508 : (prog pl).fetchMem m (pl.base + 1300#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) (Reg.gpr 0x12#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 10 2 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_50c : (prog pl).fetchMem m (pl.base + 1304#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 10 3 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_510 : (prog pl).fetchMem m (pl.base + 1308#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 10 4 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_514 : (prog pl).fetchMem m (pl.base + 1312#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0a#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 10 5 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_518 : (prog pl).fetchMem m (pl.base + 1316#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 10 6 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_51c : (prog pl).fetchMem m (pl.base + 1320#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 10 7 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_520 : (prog pl).fetchMem m (pl.base + 1324#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0a#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 10 8 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_524 : (prog pl).fetchMem m (pl.base + 1328#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 10 9 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_528 : (prog pl).fetchMem m (pl.base + 1332#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 10 10 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_52c : (prog pl).fetchMem m (pl.base + 1336#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0a#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 10 11 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_530 : (prog pl).fetchMem m (pl.base + 1340#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 10 12 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_534 : (prog pl).fetchMem m (pl.base + 1344#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 10 13 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_538 : (prog pl).fetchMem m (pl.base + 1348#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0a#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 10 14 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_53c : (prog pl).fetchMem m (pl.base + 1352#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 10 15 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_540 : (prog pl).fetchMem m (pl.base + 1356#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 10 16 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_544 : (prog pl).fetchMem m (pl.base + 1360#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0a#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 10 17 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_548 : (prog pl).fetchMem m (pl.base + 1364#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 10 18 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_54c : (prog pl).fetchMem m (pl.base + 1368#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 10 19 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_550 : (prog pl).fetchMem m (pl.base + 1372#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0a#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 10 20 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_554 : (prog pl).fetchMem m (pl.base + 1376#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 10 21 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_558 : (prog pl).fetchMem m (pl.base + 1380#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 10 22 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_55c : (prog pl).fetchMem m (pl.base + 1384#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0a#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 10 23 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_560 : (prog pl).fetchMem m (pl.base + 1388#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 10 24 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_564 : (prog pl).fetchMem m (pl.base + 1392#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 10 25 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_568 : (prog pl).fetchMem m (pl.base + 1396#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 8 63) :=
  fetch_at hP hCL 10 26 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_56c : (prog pl).fetchMem m (pl.base + 1400#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x0a#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x0a#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 10 27 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_570 : (prog pl).fetchMem m (pl.base + 1404#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 10 28 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_574 : (prog pl).fetchMem m (pl.base + 1408#64) = some (Instr.ldr (RegWidth.W64) (MemWidth.X64) false (Reg.gpr 0x0a#5) (AddrMode.Offset (Reg.gpr 0x01#5) 0x0000000000000020#64)) :=
  fetch_at hP hCL 10 29 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_578 : (prog pl).fetchMem m (pl.base + 1412#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.ADD) (Reg.gpr 0x01#5) (Reg.gpr 0x01#5) 0x028#12 false) :=
  fetch_at hP hCL 10 30 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_57c : (prog pl).fetchMem m (pl.base + 1416#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 10 31 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_580 : (prog pl).fetchMem m (pl.base + 1420#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 11 0 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_584 : (prog pl).fetchMem m (pl.base + 1424#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 11 1 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_588 : (prog pl).fetchMem m (pl.base + 1428#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 11 2 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_58c : (prog pl).fetchMem m (pl.base + 1432#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 11 3 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_590 : (prog pl).fetchMem m (pl.base + 1436#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 11 4 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_594 : (prog pl).fetchMem m (pl.base + 1440#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 11 5 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_598 : (prog pl).fetchMem m (pl.base + 1444#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 11 6 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_59c : (prog pl).fetchMem m (pl.base + 1448#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 11 7 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5a0 : (prog pl).fetchMem m (pl.base + 1452#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 11 8 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5a4 : (prog pl).fetchMem m (pl.base + 1456#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 11 9 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5a8 : (prog pl).fetchMem m (pl.base + 1460#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 11 10 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5ac : (prog pl).fetchMem m (pl.base + 1464#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 11 11 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5b0 : (prog pl).fetchMem m (pl.base + 1468#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 11 12 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5b4 : (prog pl).fetchMem m (pl.base + 1472#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 11 13 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5b8 : (prog pl).fetchMem m (pl.base + 1476#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 11 14 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5bc : (prog pl).fetchMem m (pl.base + 1480#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 11 15 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5c0 : (prog pl).fetchMem m (pl.base + 1484#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 11 16 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5c4 : (prog pl).fetchMem m (pl.base + 1488#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 11 17 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5c8 : (prog pl).fetchMem m (pl.base + 1492#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 11 18 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5cc : (prog pl).fetchMem m (pl.base + 1496#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 11 19 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5d0 : (prog pl).fetchMem m (pl.base + 1500#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 11 20 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5d4 : (prog pl).fetchMem m (pl.base + 1504#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 11 21 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5d8 : (prog pl).fetchMem m (pl.base + 1508#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 8 63) :=
  fetch_at hP hCL 11 22 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5dc : (prog pl).fetchMem m (pl.base + 1512#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 11 23 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5e0 : (prog pl).fetchMem m (pl.base + 1516#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 11 24 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5e4 : (prog pl).fetchMem m (pl.base + 1520#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x0a#5) (Reg.gpr 0x0e#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 11 25 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5e8 : (prog pl).fetchMem m (pl.base + 1524#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 11 26 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5ec : (prog pl).fetchMem m (pl.base + 1528#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 11 27 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5f0 : (prog pl).fetchMem m (pl.base + 1532#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 11 28 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5f4 : (prog pl).fetchMem m (pl.base + 1536#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 11 29 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5f8 : (prog pl).fetchMem m (pl.base + 1540#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 11 30 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_5fc : (prog pl).fetchMem m (pl.base + 1544#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 11 31 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_600 : (prog pl).fetchMem m (pl.base + 1548#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 12 0 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_604 : (prog pl).fetchMem m (pl.base + 1552#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 12 1 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_608 : (prog pl).fetchMem m (pl.base + 1556#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 12 2 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_60c : (prog pl).fetchMem m (pl.base + 1560#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 12 3 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_610 : (prog pl).fetchMem m (pl.base + 1564#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 12 4 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_614 : (prog pl).fetchMem m (pl.base + 1568#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 12 5 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_618 : (prog pl).fetchMem m (pl.base + 1572#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 12 6 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_61c : (prog pl).fetchMem m (pl.base + 1576#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 12 7 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_620 : (prog pl).fetchMem m (pl.base + 1580#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 12 8 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_624 : (prog pl).fetchMem m (pl.base + 1584#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 12 9 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_628 : (prog pl).fetchMem m (pl.base + 1588#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 12 10 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_62c : (prog pl).fetchMem m (pl.base + 1592#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 12 11 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_630 : (prog pl).fetchMem m (pl.base + 1596#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 12 12 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_634 : (prog pl).fetchMem m (pl.base + 1600#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 12 13 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_638 : (prog pl).fetchMem m (pl.base + 1604#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 12 14 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_63c : (prog pl).fetchMem m (pl.base + 1608#64) = some (Instr.logicalShift (RegWidth.W64) (LogicalOp.EOR) (Reg.gpr 0x08#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSR) 8) :=
  fetch_at hP hCL 12 15 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_640 : (prog pl).fetchMem m (pl.base + 1612#64) = some (Instr.logicalImm (RegWidth.W64) (LogicalOp.AND) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) 0x00000000000000ff#64) :=
  fetch_at hP hCL 12 16 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_644 : (prog pl).fetchMem m (pl.base + 1616#64) = some (Instr.bitfield (RegWidth.W64) (BitfieldOp.UBFM) (Reg.gpr 0x08#5) (Reg.gpr 0x08#5) 8 63) :=
  fetch_at hP hCL 12 17 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_648 : (prog pl).fetchMem m (pl.base + 1620#64) = some (Instr.ldr (RegWidth.W32) (MemWidth.W32) false (Reg.gpr 0x09#5) (AddrMode.RegOffset (Reg.gpr 0x0d#5) (Reg.gpr 0x09#5) (ExtendType.UXTX) 2)) :=
  fetch_at hP hCL 12 18 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_64c : (prog pl).fetchMem m (pl.base + 1624#64) = some (Instr.logicalShift (RegWidth.W32) (LogicalOp.EOR) (Reg.gpr 0x09#5) (Reg.gpr 0x09#5) (Reg.gpr 0x08#5) (ShiftType.LSL) 0) :=
  fetch_at hP hCL 12 19 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_650 : (prog pl).fetchMem m (pl.base + 1628#64) = some (Instr.addSubImm (RegWidth.W64) (AddSubOp.SUBS) (Reg.xzr) (Reg.gpr 0x02#5) 0x008#12 false) :=
  fetch_at hP hCL 12 20 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem f_654 : (prog pl).fetchMem m (pl.base + 1632#64) = some (Instr.bCond (CondCode.CC) 0xfffffffffffff9e4#64) :=
  fetch_at hP hCL 12 21 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

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

theorem cell_union_left {h1 h2 : Heap} {a : BitVec 64} {c : HeapCell}
    (h : h1.phys a = some c) : (h1.union h2).phys a = some c := by
  simp [Heap.union, h]

theorem cell_union_right {h1 h2 : Heap} (hd : h1.Disjoint h2) {a : BitVec 64} {c : HeapCell}
    (h : h2.phys a = some c) : (h1.union h2).phys a = some c := by
  rcases hd.1 a with h0 | h0 | ⟨b', e1, e2⟩
  · simp [Heap.union, h0, h]
  · rw [h] at h0; cases h0
  · rw [h] at e2; cases e2; simp [Heap.union, e1]

theorem sep_left {P Q : SepProp} {h : Heap} (hs : (P ∗ Q).holds h) {a : BitVec 64} {c : HeapCell}
    (hP : ∀ h1, P.holds h1 → h1.phys a = some c) : h.phys a = some c := by
  obtain ⟨h1, h2, _, rfl, p1, _⟩ := hs
  exact cell_union_left (hP h1 p1)

theorem sep_right {P Q : SepProp} {h : Heap} (hs : (P ∗ Q).holds h) {a : BitVec 64} {c : HeapCell}
    (hQ : ∀ h2, Q.holds h2 → h2.phys a = some c) : h.phys a = some c := by
  obtain ⟨h1, h2, hd, rfl, _, q2⟩ := hs
  exact cell_union_right hd (hQ h2 q2)

theorem ro_bytes : ∀ (bs : List (BitVec 8)) (a : BitVec 64) (h : Heap),
    (pointsToBytesRO a bs).holds h → ∀ i (hi : i < bs.length),
      h.phys (a + BitVec.ofNat 64 i) = some (.ro bs[i])
  | [], _, _, _, i, hi => by simp at hi
  | b :: bs, a, h, hs, i, hi => by
    simp only [pointsToBytesRO] at hs
    cases i with
    | zero =>
      refine sep_left hs fun h1 p1 => ?_
      simp only [pointsTo8RO] at p1
      subst p1; simp [Heap.singletonRO]
    | succ i =>
      refine sep_right hs fun h2 p2 => ?_
      have := ro_bytes bs (a + 1#64) h2 p2 i (by simp at hi; omega)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_comm] at this
      simpa using this

theorem dataInit_eq (pl : Placement) :
    zlibCrc32Lib.dataInit pl =
      (pointsToBytesRO (pl.ρ "crc_table [zlib_crc32]") zlibCrc32PlacedData0 ∗
        (pointsToBytesRO (pl.ρ "crc_braid_table [zlib_crc32]") zlibCrc32PlacedData1 ∗
          pointsToBytesRO (pl.ρ "x2n_table [zlib_crc32]") zlibCrc32PlacedData2)) := by
  simp only [PlacedLib.dataInit, zlibCrc32Lib, zlibCrc32Data, List.map, sepAll,
    PlacedLib.patchedData, List.foldl, List.replicate, List.append_nil, if_true]

/-! ## Heaps that differ only in the bytes of read-write cells of a region -/

/-- `h'` is `h` with some read-write bytes (at addresses satisfying `P`) changed. -/
def Sim (P : BitVec 64 → Prop) (h h' : Heap) : Prop :=
  (∀ a, h.phys a = h'.phys a ∨
    (P a ∧ ∃ b b' : BitVec 8, h.phys a = some (.rw b) ∧ h'.phys a = some (.rw b'))) ∧
  h.auth = h'.auth ∧ h.frag = h'.frag ∧ h.mapped = h'.mapped

theorem sim_disj_left {P : BitVec 64 → Prop} {h h' e : Heap} (hs : Sim P h h')
    (hd : h.Disjoint e) : h'.Disjoint e := by
  obtain ⟨s1, s2, s3, s4⟩ := hs
  obtain ⟨d1, d2, d3, d4, d5⟩ := hd
  refine ⟨fun a => ?_, by rw [← s2]; exact d2, by rw [← s3]; exact d3,
    by rw [← s2, ← s3]; exact d4, by rw [← s4]; exact d5⟩
  rcases s1 a with x | ⟨_, b, b', x, y⟩
  · rw [← x]; exact d1 a
  · rcases d1 a with z | z | ⟨c, z, w⟩
    · rw [x] at z; cases z
    · exact Or.inr (Or.inl z)
    · rw [x] at z; cases z

theorem sim_disj_right {P : BitVec 64 → Prop} {h h' e : Heap} (hs : Sim P h h')
    (hd : e.Disjoint h) : e.Disjoint h' := by
  obtain ⟨s1, s2, s3, s4⟩ := hs
  obtain ⟨d1, d2, d3, d4, d5⟩ := hd
  refine ⟨fun a => ?_, by rw [← s2]; exact d2, by rw [← s3]; exact d3,
    by rw [← s2, ← s3]; exact d4, by rw [← s4]; exact d5⟩
  rcases s1 a with x | ⟨_, b, b', x, y⟩
  · rw [← x]; exact d1 a
  · rcases d1 a with z | z | ⟨c, z, w⟩
    · exact Or.inl z
    · rw [x] at z; cases z
    · rw [x] at w; cases w

theorem sim_union_left {P : BitVec 64 → Prop} {h h' : Heap} (e : Heap) (hs : Sim P h h') :
    Sim P (h.union e) (h'.union e) := by
  obtain ⟨s1, s2, s3, s4⟩ := hs
  refine ⟨fun a => ?_, ?_, ?_, ?_⟩
  · rcases s1 a with x | ⟨hp, b, b', x, y⟩
    · left; simp only [Heap.union, x]
    · right; exact ⟨hp, b, b', by simp [Heap.union, x], by simp [Heap.union, y]⟩
  · simp only [Heap.union, s2]
  · simp only [Heap.union, s3]
  · simp only [Heap.union, s4]

theorem sim_union_right {P : BitVec 64 → Prop} {h h' : Heap} (e : Heap) (hs : Sim P h h') :
    Sim P (e.union h) (e.union h') := by
  obtain ⟨s1, s2, s3, s4⟩ := hs
  refine ⟨fun a => ?_, ?_, ?_, ?_⟩
  · cases he : e.phys a with
    | some c => left; simp [Heap.union, he]
    | none =>
      rcases s1 a with x | ⟨hp, b, b', x, y⟩
      · left; simp [Heap.union, he, x]
      · right; exact ⟨hp, b, b', by simp [Heap.union, he, x], by simp [Heap.union, he, y]⟩
  · simp only [Heap.union, s2]
  · simp only [Heap.union, s3]
  · simp only [Heap.union, s4]

theorem sim_region (base : BitVec 64) (n : ℕ) (m0 m : Memory) :
    Sim (InRegion base n) (regionHeap base n m0) (regionHeap base n m) := by
  refine ⟨fun a => ?_, rfl, rfl, rfl⟩
  by_cases hin : InRegion base n a
  · right; exact ⟨hin, m0.read8 a, m.read8 a, by simp [regionHeap, hin], by simp [regionHeap, hin]⟩
  · left; simp [regionHeap, hin]

/-! ## Memory cells -/

theorem cells_facts {m m' : Memory} {a : BitVec 64} (h : m.cells a = m'.cells a) :
    m.read8 a = m'.read8 a ∧ m.perm a = m'.perm a ∧ m.isLazyFree a = m'.isLazyFree a ∧
      m.isAnon a = m'.isAnon a := by
  simp [Memory.read8, Memory.perm, Memory.isLazyFree, Memory.isAnon, h]

theorem cells_write8_ne {m : Memory} {x a : BitVec 64} {v : BitVec 8} (h : a ≠ x) :
    (m.write8 x v).cells a = m.cells a := by
  simp [Memory.write8, h]

theorem perm_write8 (m : Memory) (x a : BitVec 64) (v : BitVec 8) :
    (m.write8 x v).perm a = m.perm a := by
  by_cases h : a = x
  · subst h
    simp only [Memory.write8, Memory.perm, Memory.rawPerm, if_true]
    rcases m.cells a with _ | ⟨_ | p, b⟩ <;> rfl
  · exact (cells_facts (cells_write8_ne h)).2.1

theorem isAnon_write8 (m : Memory) (x a : BitVec 64) (v : BitVec 8) :
    (m.write8 x v).isAnon a = m.isAnon a := by
  by_cases h : a = x
  · subst h
    simp only [Memory.write8, Memory.isAnon, Memory.rawPerm, if_true]
    rcases m.cells a with _ | ⟨_ | p, b⟩ <;> rfl
  · exact (cells_facts (cells_write8_ne h)).2.2.2

theorem lazy_write8 {m : Memory} {x a : BitVec 64} (v : BitVec 8) (hl : m.isLazyFree a = false) :
    (m.write8 x v).isLazyFree a = false := by
  by_cases h : a = x
  · subst h
    simp only [Memory.write8, Memory.isLazyFree, Memory.rawPerm, if_true]
    rcases m.cells a with _ | ⟨_ | p, b⟩ <;> rfl
  · rw [(cells_facts (cells_write8_ne h)).2.2.1, hl]

theorem read8_write8 (m : Memory) (x a : BitVec 64) (v : BitVec 8) :
    (m.write8 x v).read8 a = if a = x then v else m.read8 a := by
  by_cases h : a = x
  · subst h; simp [Memory.write8, Memory.read8]
  · simp only [h, if_false]; exact (cells_facts (cells_write8_ne h)).1

theorem perm_write64 (m : Memory) (x a v : BitVec 64) : (m.write64 x v).perm a = m.perm a := by
  simp only [Memory.write64, perm_write8]

theorem isAnon_write64 (m : Memory) (x a v : BitVec 64) :
    (m.write64 x v).isAnon a = m.isAnon a := by
  simp only [Memory.write64, isAnon_write8]

theorem lazy_write64 {m : Memory} {x a : BitVec 64} (v : BitVec 64) (hl : m.isLazyFree a = false) :
    (m.write64 x v).isLazyFree a = false := by
  simp only [Memory.write64]
  repeat apply lazy_write8
  exact hl

theorem cells_write64 {m : Memory} {x a : BitVec 64} (v : BitVec 64)
    (h : ∀ k, k < 8 → a ≠ x + BitVec.ofNat 64 k) : (m.write64 x v).cells a = m.cells a := by
  simp only [Memory.write64]
  rw [cells_write8_ne (h 7 (by omega)), cells_write8_ne (h 6 (by omega)),
    cells_write8_ne (h 5 (by omega)), cells_write8_ne (h 4 (by omega)),
    cells_write8_ne (h 3 (by omega)), cells_write8_ne (h 2 (by omega)),
    cells_write8_ne (h 1 (by omega)), cells_write8_ne (h 0 (by omega))]

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

theorem bytes_concat (v : BitVec 64) :
    v.extractLsb' 56 8 ++ v.extractLsb' 48 8 ++ v.extractLsb' 40 8 ++ v.extractLsb' 32 8 ++
      v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

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

theorem slot_ne (i j k k' : ℕ) (hi : i < 12) (hj : j < 12) (hk : k < 8) (hk' : k' < 8)
    (hij : i ≠ j) : slot s0 i + BitVec.ofNat 64 k ≠ slot s0 j + BitVec.ofNat 64 k' := by
  intro h
  have := congrArg (fun x => (x - (s0.sp - 96#64)).toNat) h
  rw [slot_off i k hi hk, slot_off j k' hj hk'] at this
  omega

end

/-! ## Precondition facts -/

theorem roOut_of_cells {s0 : State} {H : Heap} (hm : H.Matches s0.mem)
    (hreg : ∀ a, InRegion (s0.sp - 96#64) 96 a → ∃ b, H.phys a = some (.rw b))
    {a : BitVec 64} {bs : List (BitVec 8)}
    (hc : ∀ i (hi : i < bs.length), H.phys (a + BitVec.ofNat 64 i) = some (.ro bs[i])) :
    RoOut s0 a bs := by
  refine ⟨fun i hi => hm.1 _ _ (hc i hi), fun i hi hin => ?_⟩
  obtain ⟨b, hb⟩ := hreg _ hin
  rw [hc i hi] at hb; cases hb

section
variable {pl : Placement} {s0 : State} {R : SepProp} {m : Memory}

theorem pre_facts {bs : List (BitVec 8)}
    (hpre : s0.mem ⊨ (crc32zSpec pl).pre (some bs) s0 ∗ R) :
    s0.readReg64 (.gpr 1#5) ≠ 0#64 ∧ (s0.readReg64 (.gpr 2#5)).toNat = bs.length ∧
    RoOut s0 (s0.readReg64 (.gpr 1#5)) bs ∧
    RoOut s0 (pl.ρ crcTabSym) zlibCrc32PlacedData0 ∧
    RoOut s0 (pl.ρ braidTabSym) zlibCrc32PlacedData1 ∧
    FrameOk s0 s0.mem := by
  obtain ⟨H, ⟨h1, h2, hd12, rfl, hP, hR⟩, hm⟩ := hpre
  simp only [crc32zSpec] at hP
  obtain ⟨g1, g2, hdg, rfl, ⟨rfl, hφ⟩, hP2⟩ := hP
  obtain ⟨hb, g3, hdb, rfl, hbuf, hP3⟩ := hP2
  obtain ⟨hf, hD, hdf, rfl, ⟨m0, hfr⟩, hdat⟩ := hP3
  have hfr' : hf = regionHeap (s0.sp - 96#64) 96 m0 := hfr
  subst hfr'
  have hreg : ∀ a, InRegion (s0.sp - 96#64) 96 a → ∃ b,
      ((Heap.empty.union (hb.union ((regionHeap (s0.sp - 96#64) 96 m0).union hD))).union
        h2).phys a = some (.rw b) := fun a hin =>
    ⟨m0.read8 a, cell_union_left (cell_union_right hdg (cell_union_right hdb
      (cell_union_left (by simp [regionHeap, hin]))))⟩
  rw [dataInit_eq] at hdat
  obtain ⟨d0, d12, hd0, rfl, p0, p12⟩ := hdat
  obtain ⟨d1, d2, hd1, rfl, p1, _⟩ := p12
  refine ⟨hφ.1, hφ.2, roOut_of_cells hm hreg fun i hi => ?_, roOut_of_cells hm hreg fun i hi => ?_,
    roOut_of_cells hm hreg fun i hi => ?_, fun a => ⟨fun _ => rfl, fun hin => ?_⟩⟩
  · exact cell_union_left (cell_union_right hdg (cell_union_left (ro_bytes _ _ _ hbuf i hi)))
  · exact cell_union_left (cell_union_right hdg (cell_union_right hdb (cell_union_right hdf
      (cell_union_left (ro_bytes _ _ _ p0 i hi)))))
  · exact cell_union_left (cell_union_right hdg (cell_union_right hdb (cell_union_right hdf
      (cell_union_right hd0 (cell_union_left (ro_bytes _ _ _ p1 i hi))))))
  · obtain ⟨b, hb⟩ := hreg a hin
    exact ⟨(hm.1 a _ hb).2.1, (hm.1 a _ hb).2.2, rfl⟩

theorem pre_none_facts (hpre : s0.mem ⊨ (crc32zSpec pl).pre none s0 ∗ R) :
    s0.readReg64 (.gpr 1#5) = 0#64 := by
  obtain ⟨H, ⟨h1, h2, hd12, rfl, hP, hR⟩, hm⟩ := hpre
  simp only [crc32zSpec] at hP
  obtain ⟨g1, g2, hdg, rfl, ⟨_, hφ⟩, _⟩ := hP
  exact hφ

/-- `post_some` with the extra hypothesis that the frame keeps its `isAnon` bits. -/
theorem post_some_of_anon {bs : List (BitVec 8)}
    (hpre : s0.mem ⊨ (crc32zSpec pl).pre (some bs) s0 ∗ R) (hF : FrameOk s0 m)
    (hA : ∀ a, InRegion (s0.sp - 96#64) 96 a → m.isAnon a = s0.mem.isAnon a) (sf : State)
    (hm : sf.mem = m)
    (hv : Holds32 (sf.readReg64 (.gpr 0#5)) (crc32Poly ((s0.readReg64 (.gpr 0#5)).setWidth 32) bs)) :
    sf.mem ⊨ (crc32zSpec pl).post (some bs) s0 sf ∗ R := by
  rw [hm]
  obtain ⟨H, ⟨h1, h2, hd12, rfl, hP, hR⟩, hmt⟩ := hpre
  simp only [crc32zSpec] at hP
  obtain ⟨g1, g2, hdg, rfl, ⟨rfl, hφ⟩, hP2⟩ := hP
  obtain ⟨hb, g3, hdb, rfl, hbuf, hP3⟩ := hP2
  obtain ⟨hf, hD, hdf, rfl, ⟨m0, hfr⟩, hdat⟩ := hP3
  have hfr' : hf = regionHeap (s0.sp - 96#64) 96 m0 := hfr
  subst hfr'
  have S0 := sim_region (s0.sp - 96#64) 96 m0 m
  have dfD := sim_disj_left S0 hdf
  have S1 := sim_union_left hD S0
  have dbD := sim_disj_right S1 hdb
  have S2 := sim_union_right hb S1
  have dg := sim_disj_right S2 hdg
  have S3 := sim_union_right Heap.empty S2
  have d12 := sim_disj_left S3 hd12
  have S4 := sim_union_left h2 S3
  refine ⟨_, ⟨_, h2, d12, rfl, ?_, hR⟩, ?_⟩
  · simp only [crc32zSpec]
    exact ⟨Heap.empty, _, dg, rfl, ⟨rfl, hv⟩, hb, _, dbD, rfl, hbuf, _, hD, dfD, rfl, ⟨m, rfl⟩,
      hdat⟩
  · obtain ⟨s1, s2, s3, s4⟩ := S4
    refine ⟨fun a c hc => ?_, ?_, fun a ha => ?_⟩
    · by_cases hin : InRegion (s0.sp - 96#64) 96 a
      · have e := cell_union_left (h2 := h2) (cell_union_right dg (cell_union_right dbD
          (cell_union_left (h2 := hD) (show (regionHeap (s0.sp - 96#64) 96 m).phys a =
            some (.rw (m.read8 a)) by simp [regionHeap, hin]))))
        rw [e] at hc; cases hc
        exact ⟨rfl, ((hF a).2 hin).1, ((hF a).2 hin).2.1⟩
      · rcases s1 a with x | ⟨hp, _⟩
        · rw [← x] at hc
          have := hmt.1 a c hc
          obtain ⟨e1, e2, e3, _⟩ := cells_facts ((hF a).1 hin)
          cases c <;> (simp only [e1, e2, e3]; exact this)
        · exact absurd hp hin
    · obtain ⟨B, hB⟩ := hmt.2.1
      exact ⟨B, fun γ hγ k => by rw [← s2, ← s3]; exact hB γ hγ k⟩
    · rw [← s4] at ha
      obtain ⟨p1, p2⟩ := hmt.2.2 a ha
      by_cases hin : InRegion (s0.sp - 96#64) 96 a
      · rw [hA a hin, (hF a).2 hin |>.1]; exact ⟨rfl, p2⟩
      · obtain ⟨_, e2, _, e4⟩ := cells_facts ((hF a).1 hin)
        rw [e2, e4]; exact ⟨p1, p2⟩

theorem post_some {bs : List (BitVec 8)}
    (hpre : s0.mem ⊨ (crc32zSpec pl).pre (some bs) s0 ∗ R) (hF : FrameOk s0 m) (sf : State)
    (hm : sf.mem = m)
    (hv : Holds32 (sf.readReg64 (.gpr 0#5)) (crc32Poly ((s0.readReg64 (.gpr 0#5)).setWidth 32) bs)) :
    sf.mem ⊨ (crc32zSpec pl).post (some bs) s0 sf ∗ R :=
  post_some_of_anon hpre hF (fun a hin => ((hF a).2 hin).2.2) sf hm hv

/- (History) `post_some` was first stated with a weaker `FrameOk`: it is false. `FrameOk s0 m` does not
constrain `m.isAnon` on the frame, but the frame `R` may own mapping tokens (`Heap.mapped`) on the
frame's addresses, and `Heap.Matches` then demands `m.isAnon a = true` there. Use
`post_some_of_anon` (extra hypothesis: the frame keeps its `isAnon` bits; `isAnon_write64` shows
every `write64` keeps them). -/

theorem post_none (hpre : s0.mem ⊨ (crc32zSpec pl).pre none s0 ∗ R) (sf : State)
    (hm : sf.mem = s0.mem) (hv : sf.readReg64 (.gpr 0#5) = 0#64) :
    sf.mem ⊨ (crc32zSpec pl).post none s0 sf ∗ R := by
  rw [hm]
  obtain ⟨H, ⟨h1, h2, hd, rfl, hP, hR⟩, hmt⟩ := hpre
  refine ⟨_, ⟨h1, h2, hd, rfl, ?_, hR⟩, hmt⟩
  simp only [crc32zSpec] at hP ⊢
  obtain ⟨g1, g2, hd', rfl, ⟨he, _⟩, hrest⟩ := hP
  exact ⟨g1, g2, hd', rfl, ⟨he, hv⟩, hrest⟩

theorem frameOk_write64 (hF : FrameOk s0 m) (j : ℕ) (hj : j < 12) (v : BitVec 64) :
    m.canWrite (slot s0 j) 8 = true ∧ FrameOk s0 (m.write64 (slot s0 j) v) := by
  refine ⟨?_, fun a => ⟨fun hin => ?_, fun hin => ?_⟩⟩
  · simp only [Memory.canWrite]
    refine allPerm_of 8 _ fun k hk => ?_
    rw [((hF _).2 (inRegion_slot j k hj hk)).1]; rfl
  · rw [cells_write64 v fun k hk h => hin (by rw [h]; exact inRegion_slot j k hj hk)]
    exact (hF a).1 hin
  · exact ⟨by rw [perm_write64]; exact ((hF a).2 hin).1, lazy_write64 v ((hF a).2 hin).2.1,
      by rw [isAnon_write64]; exact ((hF a).2 hin).2.2⟩

theorem frameOk_canRead (hF : FrameOk s0 m) (j : ℕ) (hj : j < 12) :
    m.canRead (slot s0 j) 8 = true := by
  refine canRead_of fun k hk => ?_
  obtain ⟨h1, h2, _⟩ := (hF _).2 (inRegion_slot j k hj hk)
  rw [h1]; exact ⟨rfl, h2⟩

theorem read64_write64_same (a v : BitVec 64) : (m.write64 a v).read64 a = v := by
  simp only [Memory.read64, Memory.write64, read8_write8]
  simp
  exact bytes_concat v

theorem read64_write64_slot (i j : ℕ) (hi : i < 12) (hj : j < 12) (hij : i ≠ j) (v : BitVec 64) :
    (m.write64 (slot s0 j) v).read64 (slot s0 i) = m.read64 (slot s0 i) := by
  have hr : ∀ k, k < 8 → (m.write64 (slot s0 j) v).read8 (slot s0 i + BitVec.ofNat 64 k) =
      m.read8 (slot s0 i + BitVec.ofNat 64 k) := fun k hk =>
    (cells_facts (cells_write64 v fun k' hk' => slot_ne i j k k' hi hj hk hk' hij)).1
  simp only [Memory.read64]
  rw [hr 0 (by omega), hr 1 (by omega), hr 2 (by omega), hr 3 (by omega), hr 4 (by omega),
    hr 5 (by omega), hr 6 (by omega), hr 7 (by omega)]

theorem roBytes_of_frame (hF : FrameOk s0 m) {a : BitVec 64} {bs : List (BitVec 8)}
    (h : RoOut s0 a bs) : RoBytes m a bs := by
  intro i hi
  obtain ⟨e1, e2, e3, _⟩ := cells_facts ((hF _).1 (h.2 i hi))
  rw [e1, e2, e3]
  exact h.1 i hi

theorem codeLoaded_of_frame (hF0 : FrameOk s0 s0.mem) (hF : FrameOk s0 m)
    (hCL : (prog pl).CodeLoaded s0.mem) : (prog pl).CodeLoaded m := by
  unfold Program.CodeLoaded at *
  obtain ⟨c1, c2, c3⟩ := hCL
  refine ⟨c1, c2, fun i hi => ?_⟩
  obtain ⟨r1, r2, r3⟩ := c3 i hi
  have hin : ¬ InRegion (s0.sp - 96#64) 96 ((prog pl).base + BitVec.ofNat 64 i) := by
    intro hin
    rw [((hF0 _).2 hin).1] at r2
    cases r2
  obtain ⟨e1, e2, e3, _⟩ := cells_facts ((hF _).1 hin)
  rw [e1, e2, e3]
  exact ⟨r1, r2, r3⟩

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

theorem ro_read64 {a : BitVec 64} {bs : List (BitVec 8)} (h : RoBytes m a bs) (i : ℕ)
    (hi : i + 8 ≤ bs.length) :
    m.canRead (a + BitVec.ofNat 64 i) 8 = true ∧ m.read64 (a + BitVec.ofNat 64 i) = wordLE bs i := by
  have e : ∀ k, k < 8 → m.read8 (a + BitVec.ofNat 64 i + BitVec.ofNat 64 k) =
      bs.getD (i + k) 0#8 := fun k hk => by
    rw [add_ofNat_add, List.getD_eq_getElem _ _ (by omega)]
    exact (h _ _).1
  refine ⟨canRead_of fun k hk => ?_, ?_⟩
  · rw [add_ofNat_add]; exact (h _ (by omega)).2
  · simp only [Memory.read64, wordLE]
    rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega),
      e 5 (by omega), e 6 (by omega), e 7 (by omega)]
    simp only [Nat.add_zero]

end

end ZlibCrc32.Crcz.PartB

namespace ZlibCrc32.Crcz
alias pre_facts := PartB.pre_facts
alias pre_none_facts := PartB.pre_none_facts
alias post_some := PartB.post_some
alias post_none := PartB.post_none
alias frameOk_write64 := PartB.frameOk_write64
alias frameOk_canRead := PartB.frameOk_canRead
alias read64_write64_same := PartB.read64_write64_same
alias read64_write64_slot := PartB.read64_write64_slot
alias roBytes_of_frame := PartB.roBytes_of_frame
alias codeLoaded_of_frame := PartB.codeLoaded_of_frame
alias ro_read8 := PartB.ro_read8
alias ro_read32 := PartB.ro_read32
alias ro_read64 := PartB.ro_read64
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

theorem mkS_self (s0 : State) : mkS s0 s0.mem s0.sp s0.pc s0.pstate (Regs.of s0) = s0 := by
  have hr : (⟨(Regs.of s0).get s0.regs.regs⟩ : RegFile) = s0.regs := by
    show RegFile.mk _ = RegFile.mk s0.regs.regs
    congr 1; funext i
    unfold Regs.get
    by_cases h0 : i = 0#5
    · subst h0; rfl
    rw [if_neg h0]
    by_cases h1 : i = 1#5
    · subst h1; rfl
    rw [if_neg h1]
    by_cases h2 : i = 2#5
    · subst h2; rfl
    rw [if_neg h2]
    by_cases h3 : i = 3#5
    · subst h3; rfl
    rw [if_neg h3]
    by_cases h4 : i = 4#5
    · subst h4; rfl
    rw [if_neg h4]
    by_cases h5 : i = 5#5
    · subst h5; rfl
    rw [if_neg h5]
    by_cases h6 : i = 6#5
    · subst h6; rfl
    rw [if_neg h6]
    by_cases h7 : i = 7#5
    · subst h7; rfl
    rw [if_neg h7]
    by_cases h8 : i = 8#5
    · subst h8; rfl
    rw [if_neg h8]
    by_cases h9 : i = 9#5
    · subst h9; rfl
    rw [if_neg h9]
    by_cases h10 : i = 10#5
    · subst h10; rfl
    rw [if_neg h10]
    by_cases h11 : i = 11#5
    · subst h11; rfl
    rw [if_neg h11]
    by_cases h12 : i = 12#5
    · subst h12; rfl
    rw [if_neg h12]
    by_cases h13 : i = 13#5
    · subst h13; rfl
    rw [if_neg h13]
    by_cases h14 : i = 14#5
    · subst h14; rfl
    rw [if_neg h14]
    by_cases h15 : i = 15#5
    · subst h15; rfl
    rw [if_neg h15]
    by_cases h16 : i = 16#5
    · subst h16; rfl
    rw [if_neg h16]
    by_cases h17 : i = 17#5
    · subst h17; rfl
    rw [if_neg h17]
    by_cases h18 : i = 18#5
    · subst h18; rfl
    rw [if_neg h18]
    by_cases h19 : i = 19#5
    · subst h19; rfl
    rw [if_neg h19]
    by_cases h20 : i = 20#5
    · subst h20; rfl
    rw [if_neg h20]
    by_cases h21 : i = 21#5
    · subst h21; rfl
    rw [if_neg h21]
    by_cases h22 : i = 22#5
    · subst h22; rfl
    rw [if_neg h22]
    by_cases h23 : i = 23#5
    · subst h23; rfl
    rw [if_neg h23]
    by_cases h24 : i = 24#5
    · subst h24; rfl
    rw [if_neg h24]
    by_cases h25 : i = 25#5
    · subst h25; rfl
    rw [if_neg h25]
    by_cases h26 : i = 26#5
    · subst h26; rfl
    rw [if_neg h26]
    by_cases h27 : i = 27#5
    · subst h27; rfl
    rw [if_neg h27]
    by_cases h28 : i = 28#5
    · subst h28; rfl
    rw [if_neg h28]
    by_cases h30 : i = 30#5
    · subst h30; rfl
    rw [if_neg h30]

  unfold mkS; rw [hr]

end ZlibCrc32.Crcz
end

section
/-! # Steps, `Reach`, and the per-constructor execution lemmas -/

namespace ZlibCrc32.Crcz

open Arm64 Arm64.Obj

theorem Steps.trans' {p : Program} {a b c : State} (h1 : Steps p a b) (h2 : Steps p b c) :
    Steps p a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact Steps.step h (ih h2)

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
theorem ex_cbz (w : RegWidth) (nz : Bool) (rt : Reg) (off : BitVec 64) :
    execInstWithSvc svc (.cbz w nz rt off) s =
      (let val := s.readReg w rt
       let cond := if nz then (val == 0#64) != true else val == 0#64
       if cond then s.setPC (s.pc + off) else s.advancePC) := rfl
theorem ex_addSubImm (w : RegWidth) (op : AddSubOp) (rd rn : Reg) (imm : BitVec 12) (sh : Bool) :
    execInstWithSvc svc (.addSubImm w op rd rn imm sh) s = execAddSubImm w op rd rn imm sh s := rfl
theorem ex_addSubShift (w : RegWidth) (op : AddSubOp) (rd rn rm : Reg) (sh : ShiftType) (a : Nat) :
    execInstWithSvc svc (.addSubShift w op rd rn rm sh a) s = execAddSubShift w op rd rn rm sh a s := rfl
theorem ex_logicalShift (w : RegWidth) (op : LogicalOp) (rd rn rm : Reg) (sh : ShiftType) (a : Nat) :
    execInstWithSvc svc (.logicalShift w op rd rn rm sh a) s = execLogicalShift w op rd rn rm sh a s := rfl
theorem ex_logicalImm (w : RegWidth) (op : LogicalOp) (rd rn : Reg) (mask : BitVec 64) :
    execInstWithSvc svc (.logicalImm w op rd rn mask) s = execLogicalImm w op rd rn mask s := rfl
theorem ex_moveWide (w : RegWidth) (op : MoveWideOp) (rd : Reg) (imm : BitVec 16) (hw : Nat) :
    execInstWithSvc svc (.moveWide w op rd imm hw) s = execMoveWide w op rd imm hw s := rfl
theorem ex_bitfield (w : RegWidth) (op : BitfieldOp) (rd rn : Reg) (immr imms : Nat) :
    execInstWithSvc svc (.bitfield w op rd rn immr imms) s = execBitfield w op rd rn immr imms s := rfl
theorem ex_dataProc3 (w : RegWidth) (op : DataProc3Op) (rd rn rm ra : Reg) :
    execInstWithSvc svc (.dataProc3 w op rd rn rm ra) s = execDataProc3 w op rd rn rm ra s := rfl
theorem ex_bCond (c : CondCode) (off : BitVec 64) :
    execInstWithSvc svc (.bCond c off) s =
      if ConditionHolds c s.pstate then s.setPC (s.pc + off) else s.advancePC := rfl
theorem ex_b (off : BitVec 64) : execInstWithSvc svc (.b off) s = s.setPC (s.pc + off) := rfl
theorem ex_ldr (w : RegWidth) (sz : MemWidth) (sg : Bool) (rt : Reg) (a : AddrMode) :
    execInstWithSvc svc (.ldr w sz sg rt a) s = execLdr w sz sg rt a s := rfl
theorem ex_str (sz : MemWidth) (rt : Reg) (a : AddrMode) :
    execInstWithSvc svc (.str sz rt a) s = execStr sz rt a s := rfl
theorem ex_ldp (w : RegWidth) (sg : Bool) (rt1 rt2 : Reg) (a : AddrMode) :
    execInstWithSvc svc (.ldp w sg rt1 rt2 a) s = execLdp w sg rt1 rt2 a s := rfl
theorem ex_stp (w : RegWidth) (rt1 rt2 : Reg) (a : AddrMode) :
    execInstWithSvc svc (.stp w rt1 rt2 a) s = execStp w rt1 rt2 a s := rfl
theorem ex_adr (pg : Bool) (rd : Reg) (off : BitVec 64) :
    execInstWithSvc svc (.adr pg rd off) s =
      (s.writeReg64 rd ((if pg then s.pc &&& 0xfffffffffffff000#64 else s.pc) + off)).advancePC := rfl
theorem ex_nop : execInstWithSvc svc .nop s = s.advancePC := rfl
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

theorem reach_steps {pl : Placement} {s0 s s' : State} {X : BitVec 64} (h : Steps (prog pl) s s')
    (h' : Reach pl s0 X s') : Reach pl s0 X s := by
  obtain ⟨sf, h1, h2⟩ := h'
  exact ⟨sf, Steps.trans' h h1, h2⟩



















end

end ZlibCrc32.Crcz
end

section
/-! # Flags of `cmp`/`subs`, and small shared helpers -/

namespace ZlibCrc32.Crcz

open Arm64 Arm64.Obj

theorem awc_c (x y : BitVec 64) : (AddWithCarry64 x (~~~y) true).2.c = decide (y.toNat ≤ x.toNat) := by
  simp only [AddWithCarry64, BitVec.msb_eq_decide]
  simp [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_not]
  omega

theorem awc_z (x y : BitVec 64) : (AddWithCarry64 x (~~~y) true).2.z = decide (x.toNat = y.toNat) := by
  simp only [AddWithCarry64, if_true]
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [← BitVec.toNat_inj]
  simp [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_not]
  omega

theorem awc_fst (x y : BitVec 64) : (AddWithCarry64 x (~~~y) true).1 = x - y := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_sub]
  omega

theorem cond_CS (x y : BitVec 64) :
    ConditionHolds .CS (AddWithCarry64 x (~~~y) true).2 = decide (y.toNat ≤ x.toNat) := by
  simp only [ConditionHolds, awc_c]
theorem cond_CC (x y : BitVec 64) :
    ConditionHolds .CC (AddWithCarry64 x (~~~y) true).2 = decide (x.toNat < y.toNat) := by
  simp only [ConditionHolds, awc_c]
  by_cases h : y.toNat ≤ x.toNat
  · simp [h]
  · simp [h]; omega
theorem cond_EQ (x y : BitVec 64) :
    ConditionHolds .EQ (AddWithCarry64 x (~~~y) true).2 = decide (x.toNat = y.toNat) := by
  simp only [ConditionHolds, awc_z]

theorem toNat_ofNat_lt (r : ℕ) (hr : r < 2 ^ 64) : (BitVec.ofNat 64 r).toNat = r :=
  Nat.mod_eq_of_lt hr

end ZlibCrc32.Crcz
end

section
/-! # Part R: the relocated `ADRP`/`ADD` pairs, from the published `ZlibCrc32.crc32_z_adrp_pairs` -/

namespace ZlibCrc32.Crcz.PartR

open Arm64 Arm64.Obj ZlibCrc32.Crcz

theorem pc_add (b : BitVec 64) (n k : Nat) :
    b + BitVec.ofNat 64 n + BitVec.ofNat 64 k = b + BitVec.ofNat 64 (n + k) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem pageOf_eq (x : BitVec 64) : pageOf x = (x >>> 12) <<< 12 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [pageOf, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem pageOf_toNat (x : BitVec 64) : (pageOf x).toNat = x.toNat / 4096 * 4096 := by
  rw [pageOf_eq]; simp [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]; omega

theorem page_add_lo (T : BitVec 64) : pageOf T + (T.extractLsb' 0 12).setWidth 64 = T := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, pageOf_toNat]
  simp [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat]
  have := T.isLt; omega

theorem awc_add (x y : BitVec 64) : (AddWithCarry64 x y false).1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth]; omega

theorem pair13 {pl : Placement} {s0 : State} {m : Memory} {ps : PState} {R : Regs}
    (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded m)
    (hrun : s0.status = .Running) (o : Nat) (ho : o = 28 ∨ o = 1040) (sp : BitVec 64) :
    Steps (prog pl) (mkS s0 m sp (pl.base + BitVec.ofNat 64 o) ps R)
      (mkS s0 m sp (pl.base + BitVec.ofNat 64 (o + 8)) ps { R with x13 := pl.ρ crcTabSym }) := by
  have hst := ZlibCrc32.crc32_z_adrp_pairs pl hP m hCL o 13#5 crcTabSym (by rcases ho with rfl | rfl <;> simp)
  have p4 := pc_add pl.base o 4
  have p8 := pc_add pl.base (o + 4) 4
  rw [show o + 4 + 4 = o + 8 by omega] at p8
  rcases hst with ⟨hf1, hf2⟩ | ⟨hf1, hf2⟩
  · refine Steps.step (stepM hrun hf1) ?_
    rw [ex_adr]; simp only [if_true, wr_x13, mkS_advancePC, mkS_pc]; rw [p4]
    refine Steps.step (stepM hrun hf2) ?_
    rw [ex_addSubImm]
    simp only [execAddSubImm, State.readReg, rd_x13, evalAddSub, awc_add, State.writeReg, wr_x13,
      mkS_advancePC, Bool.false_eq_true, if_false]
    rw [p8]
    have e : ∀ a b : BitVec 64, a + (b - a) = b := by intro a b; bv_omega
    rw [show (pl.base + BitVec.ofNat 64 o) &&& 0xfffffffffffff000#64 =
      pageOf (pl.base + BitVec.ofNat 64 o) from rfl, e, page_add_lo]
    exact Steps.refl _
  · refine Steps.step (stepM hrun hf1) ?_
    rw [ex_nop]; simp only [mkS_advancePC]; rw [p4]
    refine Steps.step (stepM hrun hf2) ?_
    rw [ex_adr]; simp only [Bool.false_eq_true, if_false, wr_x13, mkS_advancePC, mkS_pc]
    rw [p8, show pl.base + BitVec.ofNat 64 (o + 4) + (pl.ρ crcTabSym - (pl.base + BitVec.ofNat 64 (o + 4))) =
      pl.ρ crcTabSym by bv_omega]
    exact Steps.refl _

theorem pair12 {pl : Placement} {s0 : State} {m : Memory} {ps : PState} {R : Regs}
    (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded m)
    (hrun : s0.status = .Running) (o : Nat) (ho : o = 456) (sp : BitVec 64) :
    Steps (prog pl) (mkS s0 m sp (pl.base + BitVec.ofNat 64 o) ps R)
      (mkS s0 m sp (pl.base + BitVec.ofNat 64 (o + 8)) ps { R with x12 := pl.ρ braidTabSym }) := by
  have hst := ZlibCrc32.crc32_z_adrp_pairs pl hP m hCL o 12#5 braidTabSym (by subst ho; simp)
  have p4 := pc_add pl.base o 4
  have p8 := pc_add pl.base (o + 4) 4
  rw [show o + 4 + 4 = o + 8 by omega] at p8
  rcases hst with ⟨hf1, hf2⟩ | ⟨hf1, hf2⟩
  · refine Steps.step (stepM hrun hf1) ?_
    rw [ex_adr]; simp only [if_true, wr_x12, mkS_advancePC, mkS_pc]; rw [p4]
    refine Steps.step (stepM hrun hf2) ?_
    rw [ex_addSubImm]
    simp only [execAddSubImm, State.readReg, rd_x12, evalAddSub, awc_add, State.writeReg, wr_x12,
      mkS_advancePC, Bool.false_eq_true, if_false]
    rw [p8]
    have e : ∀ a b : BitVec 64, a + (b - a) = b := by intro a b; bv_omega
    rw [show (pl.base + BitVec.ofNat 64 o) &&& 0xfffffffffffff000#64 =
      pageOf (pl.base + BitVec.ofNat 64 o) from rfl, e, page_add_lo]
    exact Steps.refl _
  · refine Steps.step (stepM hrun hf1) ?_
    rw [ex_nop]; simp only [mkS_advancePC]; rw [p4]
    refine Steps.step (stepM hrun hf2) ?_
    rw [ex_adr]; simp only [Bool.false_eq_true, if_false, wr_x12, mkS_advancePC, mkS_pc]
    rw [p8, show pl.base + BitVec.ofNat 64 (o + 4) + (pl.ρ braidTabSym - (pl.base + BitVec.ofNat 64 (o + 4))) =
      pl.ρ braidTabSym by bv_omega]
    exact Steps.refl _

section
variable {pl : Placement} {s0 : State} {m : Memory} {ps : PState} {R : Regs}

theorem reloc28 (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded m)
    (hrun : s0.status = .Running) (sp : BitVec 64) :
    Steps (prog pl) (mkS s0 m sp (pl.base + 28#64) ps R)
      (mkS s0 m sp (pl.base + 36#64) ps { R with x13 := pl.ρ crcTabSym }) :=
  pair13 hP hCL hrun 28 (Or.inl rfl) sp

theorem reloc456 (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded m)
    (hrun : s0.status = .Running) (sp : BitVec 64) :
    Steps (prog pl) (mkS s0 m sp (pl.base + 456#64) ps R)
      (mkS s0 m sp (pl.base + 464#64) ps { R with x12 := pl.ρ braidTabSym }) :=
  pair12 hP hCL hrun 456 rfl sp

theorem reloc1040 (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded m)
    (hrun : s0.status = .Running) (sp : BitVec 64) :
    Steps (prog pl) (mkS s0 m sp (pl.base + 1040#64) ps R)
      (mkS s0 m sp (pl.base + 1048#64) ps { R with x13 := pl.ρ crcTabSym }) :=
  pair13 hP hCL hrun 1040 (Or.inr rfl) sp

end

end ZlibCrc32.Crcz.PartR

namespace ZlibCrc32.Crcz
alias reloc28 := PartR.reloc28
alias reloc456 := PartR.reloc456
alias reloc1040 := PartR.reloc1040
end ZlibCrc32.Crcz
end

section
namespace ZlibCrc32.Crcz
alias tail := reach_tail
alias loop8 := reach_loop8
end ZlibCrc32.Crcz
end

section
/-! # Part FS: the fold of the last braided block (`0x428 .. 0x654`) and the block split
(`0x19c .. 0x1f0`, `0x418 .. 0x424`) of `crc32_z` -/

namespace ZlibCrc32.Crcz.PartFS

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

open Arm64 Arm64.Obj ZlibCrc32.Crcz

theorem len0 : zlibCrc32PlacedData0.length = 1024 := by decide +kernel

theorem pc_add (b : BitVec 64) (N k : ℕ) :
    b + BitVec.ofNat 64 N + BitVec.ofNat 64 k = b + BitVec.ofNat 64 (N + k) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem tz (a : BitVec 32) : (a.setWidth 64).setWidth 32 = a := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

theorem idx_and (x : BitVec 64) : (x &&& 255#64).toNat < 256 := by
  rw [BitVec.toNat_and]; exact lt_of_le_of_lt Nat.and_le_right (by decide)

theorem toNat_and255 (x : BitVec 64) : (x &&& 255#64).toNat = x.toNat % 256 := by
  rw [BitVec.toNat_and, show (255#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem last_val (x : BitVec 64) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32
      (BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.setWidth 64 (T0 (x &&& 255#64).toNat))) ^^^
        BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64
          (BitVec.truncate 32 (x >>> 8)))))))) = ((wstep x).setWidth 32).setWidth 64 := by
  simp only [BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, wstep, toNat_and255]
  ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_xor]
  by_cases h : i < 32 <;> simp [h, hi]

theorem bf_lsr8 (d x : BitVec 64) : evalBitfield .W64 .UBFM d x 8 63 = x >>> 8 := by rfl

/-- The table load `ldr wT, [x13, xI, lsl #2]` from `crc_table`. -/
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
  rw [show (BitVec.truncate 32 (BitVec.zeroExtend 64 (word32 zlibCrc32PlacedData0
    i.toNat))) = T0 i.toNat from tz _]
  exact h

section
variable {pl : Placement} {s0 : State} {m : Memory} {sp : BitVec 64} {ps : PState} {X : BitVec 64}

/-- One round `and x9, x8, #0xff; ldr w9, [x13, x9, lsl #2]; eor x8, x9, x8, lsr #8`. -/
theorem rnd9 {T : BitVec 64} (hrun : s0.status = .Running) (hT : RoBytes m T zlibCrc32PlacedData0)
    (N : ℕ) (r : Regs) (h13 : r.x13 = T)
    (hf1 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 N) =
      some (.logicalImm .W64 .AND (.gpr 9#5) (.gpr 8#5) 0xff#64))
    (hf2 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 4)) =
      some (.ldr .W32 .W32 false (.gpr 9#5) (.RegOffset (.gpr 13#5) (.gpr 9#5) .UXTX 2)))
    (hf3 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 8)) =
      some (.logicalShift .W64 .EOR (.gpr 8#5) (.gpr 9#5) (.gpr 8#5) .LSR 8))
    (hk : ∀ v, Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 (N + 12)) ps
      { r with x8 := wstep r.x8, x9 := v })) :
    Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 N) ps r) := by
  refine reach_step (stepM hrun hf1) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add]
  refine ldrT0 hrun hf2 hT (by simpa only [rd_x13] using h13) (idx_and _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add]
  refine reach_step (stepM hrun hf3) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add]
  rw [show N + 4 + 4 + 4 = N + 12 by omega]
  simp only [Nat.reduceMod, toNat_and255]
  exact hk _

/-- The same round with `x10` as the index/table register. -/
theorem rnd10 {T : BitVec 64} (hrun : s0.status = .Running) (hT : RoBytes m T zlibCrc32PlacedData0)
    (N : ℕ) (r : Regs) (h13 : r.x13 = T)
    (hf1 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 N) =
      some (.logicalImm .W64 .AND (.gpr 10#5) (.gpr 8#5) 0xff#64))
    (hf2 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 4)) =
      some (.ldr .W32 .W32 false (.gpr 10#5) (.RegOffset (.gpr 13#5) (.gpr 10#5) .UXTX 2)))
    (hf3 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 8)) =
      some (.logicalShift .W64 .EOR (.gpr 8#5) (.gpr 10#5) (.gpr 8#5) .LSR 8))
    (hk : ∀ v, Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 (N + 12)) ps
      { r with x8 := wstep r.x8, x10 := v })) :
    Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 N) ps r) := by
  refine reach_step (stepM hrun hf1) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add]
  refine ldrT0 hrun hf2 hT (by simpa only [rd_x13] using h13) (idx_and _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add]
  refine reach_step (stepM hrun hf3) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add]
  rw [show N + 4 + 4 + 4 = N + 12 by omega]
  simp only [Nat.reduceMod, toNat_and255]
  exact hk _

/-- Last round, `x9` index, result in `w8`. -/
theorem last98 {T : BitVec 64} (hrun : s0.status = .Running) (hT : RoBytes m T zlibCrc32PlacedData0)
    (N : ℕ) (r : Regs) (h13 : r.x13 = T)
    (hf1 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 N) =
      some (.logicalImm .W64 .AND (.gpr 9#5) (.gpr 8#5) 0xff#64))
    (hf2 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 4)) =
      some (.bitfield .W64 .UBFM (.gpr 8#5) (.gpr 8#5) 8 63))
    (hf3 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 8)) =
      some (.ldr .W32 .W32 false (.gpr 9#5) (.RegOffset (.gpr 13#5) (.gpr 9#5) .UXTX 2)))
    (hf4 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 12)) =
      some (.logicalShift .W32 .EOR (.gpr 8#5) (.gpr 9#5) (.gpr 8#5) .LSL 0))
    (hk : ∀ v, Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 (N + 16)) ps
      { r with x8 := ((wstep r.x8).setWidth 32).setWidth 64, x9 := v })) :
    Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 N) ps r) := by
  refine reach_step (stepM hrun hf1) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add]
  refine reach_step (stepM hrun hf2) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add, bf_lsr8]
  refine ldrT0 hrun hf3 hT (by simpa only [rd_x13] using h13) (idx_and _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add]
  refine reach_step (stepM hrun hf4) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add]
  rw [show N + 4 + 4 + 4 + 4 = N + 16 by omega, last_val]
  exact hk _

/-- Last round, `x10` index, result in `w8`. -/
theorem last108 {T : BitVec 64} (hrun : s0.status = .Running) (hT : RoBytes m T zlibCrc32PlacedData0)
    (N : ℕ) (r : Regs) (h13 : r.x13 = T)
    (hf1 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 N) =
      some (.logicalImm .W64 .AND (.gpr 10#5) (.gpr 8#5) 0xff#64))
    (hf2 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 4)) =
      some (.bitfield .W64 .UBFM (.gpr 8#5) (.gpr 8#5) 8 63))
    (hf3 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 8)) =
      some (.ldr .W32 .W32 false (.gpr 10#5) (.RegOffset (.gpr 13#5) (.gpr 10#5) .UXTX 2)))
    (hf4 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 12)) =
      some (.logicalShift .W32 .EOR (.gpr 8#5) (.gpr 10#5) (.gpr 8#5) .LSL 0))
    (hk : ∀ v, Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 (N + 16)) ps
      { r with x8 := ((wstep r.x8).setWidth 32).setWidth 64, x10 := v })) :
    Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 N) ps r) := by
  refine reach_step (stepM hrun hf1) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add]
  refine reach_step (stepM hrun hf2) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add, bf_lsr8]
  refine ldrT0 hrun hf3 hT (by simpa only [rd_x13] using h13) (idx_and _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add]
  refine reach_step (stepM hrun hf4) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add]
  rw [show N + 4 + 4 + 4 + 4 = N + 16 by omega, last_val]
  exact hk _

/-- Last round, `x9` index, result in `w9`. -/
theorem last99 {T : BitVec 64} (hrun : s0.status = .Running) (hT : RoBytes m T zlibCrc32PlacedData0)
    (N : ℕ) (r : Regs) (h13 : r.x13 = T)
    (hf1 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 N) =
      some (.logicalImm .W64 .AND (.gpr 9#5) (.gpr 8#5) 0xff#64))
    (hf2 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 4)) =
      some (.bitfield .W64 .UBFM (.gpr 8#5) (.gpr 8#5) 8 63))
    (hf3 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 8)) =
      some (.ldr .W32 .W32 false (.gpr 9#5) (.RegOffset (.gpr 13#5) (.gpr 9#5) .UXTX 2)))
    (hf4 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 12)) =
      some (.logicalShift .W32 .EOR (.gpr 9#5) (.gpr 9#5) (.gpr 8#5) .LSL 0))
    (hk : ∀ v, Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 (N + 16)) ps
      { r with x8 := v, x9 := ((wstep r.x8).setWidth 32).setWidth 64 })) :
    Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 N) ps r) := by
  refine reach_step (stepM hrun hf1) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add]
  refine reach_step (stepM hrun hf2) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add, bf_lsr8]
  refine ldrT0 hrun hf3 hT (by simpa only [rd_x13] using h13) (idx_and _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add]
  refine reach_step (stepM hrun hf4) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, pc_add]
  rw [show N + 4 + 4 + 4 + 4 = N + 16 by omega, last_val]
  exact hk _


/-- The fetches of one full round with index register `x9` at `N`. -/
def F9 (pl : Placement) (m : Memory) (N : ℕ) : Prop :=
  (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 N) =
      some (.logicalImm .W64 .AND (.gpr 9#5) (.gpr 8#5) 0xff#64) ∧
  (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 4)) =
      some (.ldr .W32 .W32 false (.gpr 9#5) (.RegOffset (.gpr 13#5) (.gpr 9#5) .UXTX 2)) ∧
  (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 8)) =
      some (.logicalShift .W64 .EOR (.gpr 8#5) (.gpr 9#5) (.gpr 8#5) .LSR 8)

/-- The fetches of one full round with index register `x10` at `N`. -/
def F10 (pl : Placement) (m : Memory) (N : ℕ) : Prop :=
  (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 N) =
      some (.logicalImm .W64 .AND (.gpr 10#5) (.gpr 8#5) 0xff#64) ∧
  (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 4)) =
      some (.ldr .W32 .W32 false (.gpr 10#5) (.RegOffset (.gpr 13#5) (.gpr 10#5) .UXTX 2)) ∧
  (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 8)) =
      some (.logicalShift .W64 .EOR (.gpr 8#5) (.gpr 10#5) (.gpr 8#5) .LSR 8)

theorem rounds9 {T : BitVec 64} (hrun : s0.status = .Running)
    (hT : RoBytes m T zlibCrc32PlacedData0) (k : ℕ) : ∀ (N : ℕ) (r : Regs), r.x13 = T →
    (∀ j, j < k → F9 pl m (N + 12 * j)) →
    (∀ v, Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 (N + 12 * k)) ps
      { r with x8 := wstep^[k] r.x8, x9 := v })) →
    Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 N) ps r) := by
  induction k with
  | zero => intro N r h13 hf hk; exact hk r.x9
  | succ k ih =>
    intro N r h13 hf hk
    obtain ⟨f1, f2, f3⟩ := hf 0 (by omega)
    refine rnd9 hrun hT N r h13 f1 f2 f3 fun v => ?_
    refine ih (N + 12) _ h13 (fun j hj => ?_) fun v' => ?_
    · have := hf (j + 1) (by omega)
      rwa [show N + 12 * (j + 1) = N + 12 + 12 * j by ring] at this
    · have := hk v'
      rw [show N + 12 * (k + 1) = N + 12 + 12 * k by ring] at this
      exact this

theorem rounds10 {T : BitVec 64} (hrun : s0.status = .Running)
    (hT : RoBytes m T zlibCrc32PlacedData0) (k : ℕ) : ∀ (N : ℕ) (r : Regs), r.x13 = T →
    (∀ j, j < k → F10 pl m (N + 12 * j)) →
    (∀ v, Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 (N + 12 * k)) ps
      { r with x8 := wstep^[k] r.x8, x10 := v })) →
    Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 N) ps r) := by
  induction k with
  | zero => intro N r h13 hf hk; exact hk r.x10
  | succ k ih =>
    intro N r h13 hf hk
    obtain ⟨f1, f2, f3⟩ := hf 0 (by omega)
    refine rnd10 hrun hT N r h13 f1 f2 f3 fun v => ?_
    refine ih (N + 12) _ h13 (fun j hj => ?_) fun v' => ?_
    · have := hf (j + 1) (by omega)
      rwa [show N + 12 * (j + 1) = N + 12 + 12 * j by ring] at this
    · have := hk v'
      rw [show N + 12 * (k + 1) = N + 12 + 12 * k by ring] at this
      exact this

theorem crcWord_val (c : BitVec 32) (w : BitVec 64) :
    ((wstep (wstep^[7] (w ^^^ c.setWidth 64))).setWidth 32).setWidth 64 =
      (crcWord c w).setWidth 64 := by
  rw [← Function.iterate_succ_apply' wstep 7, BitVec.xor_comm]; rfl

/-- `crc_word(c ^ w)`: seven rounds and the 32-bit last round, `x9` index, result in `x8`. -/
theorem word98 {T : BitVec 64} (hrun : s0.status = .Running)
    (hT : RoBytes m T zlibCrc32PlacedData0) (N : ℕ) (r : Regs) (h13 : r.x13 = T)
    (c : BitVec 32) (w : BitVec 64) (hx : r.x8 = w ^^^ c.setWidth 64)
    (hf : ∀ j, j < 7 → F9 pl m (N + 12 * j))
    (hf1 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 84)) =
      some (.logicalImm .W64 .AND (.gpr 9#5) (.gpr 8#5) 0xff#64))
    (hf2 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 84 + 4)) =
      some (.bitfield .W64 .UBFM (.gpr 8#5) (.gpr 8#5) 8 63))
    (hf3 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 84 + 8)) =
      some (.ldr .W32 .W32 false (.gpr 9#5) (.RegOffset (.gpr 13#5) (.gpr 9#5) .UXTX 2)))
    (hf4 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 84 + 12)) =
      some (.logicalShift .W32 .EOR (.gpr 8#5) (.gpr 9#5) (.gpr 8#5) .LSL 0))
    (hk : ∀ v, Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 (N + 100)) ps
      { r with x8 := (crcWord c w).setWidth 64, x9 := v })) :
    Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 N) ps r) := by
  refine rounds9 hrun hT 7 N r h13 hf fun v => ?_
  refine last98 hrun hT (N + 84) _ h13 hf1 hf2 hf3 hf4 fun v' => ?_
  have := hk v'
  rw [show N + 84 + 16 = N + 100 by omega]
  rw [← crcWord_val, ← hx] at this
  exact this

theorem word108 {T : BitVec 64} (hrun : s0.status = .Running)
    (hT : RoBytes m T zlibCrc32PlacedData0) (N : ℕ) (r : Regs) (h13 : r.x13 = T)
    (c : BitVec 32) (w : BitVec 64) (hx : r.x8 = w ^^^ c.setWidth 64)
    (hf : ∀ j, j < 7 → F10 pl m (N + 12 * j))
    (hf1 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 84)) =
      some (.logicalImm .W64 .AND (.gpr 10#5) (.gpr 8#5) 0xff#64))
    (hf2 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 84 + 4)) =
      some (.bitfield .W64 .UBFM (.gpr 8#5) (.gpr 8#5) 8 63))
    (hf3 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 84 + 8)) =
      some (.ldr .W32 .W32 false (.gpr 10#5) (.RegOffset (.gpr 13#5) (.gpr 10#5) .UXTX 2)))
    (hf4 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 84 + 12)) =
      some (.logicalShift .W32 .EOR (.gpr 8#5) (.gpr 10#5) (.gpr 8#5) .LSL 0))
    (hk : ∀ v, Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 (N + 100)) ps
      { r with x8 := (crcWord c w).setWidth 64, x10 := v })) :
    Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 N) ps r) := by
  refine rounds10 hrun hT 7 N r h13 hf fun v => ?_
  refine last108 hrun hT (N + 84) _ h13 hf1 hf2 hf3 hf4 fun v' => ?_
  have := hk v'
  rw [show N + 84 + 16 = N + 100 by omega]
  rw [← crcWord_val, ← hx] at this
  exact this

theorem word99 {T : BitVec 64} (hrun : s0.status = .Running)
    (hT : RoBytes m T zlibCrc32PlacedData0) (N : ℕ) (r : Regs) (h13 : r.x13 = T)
    (c : BitVec 32) (w : BitVec 64) (hx : r.x8 = w ^^^ c.setWidth 64)
    (hf : ∀ j, j < 7 → F9 pl m (N + 12 * j))
    (hf1 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 84)) =
      some (.logicalImm .W64 .AND (.gpr 9#5) (.gpr 8#5) 0xff#64))
    (hf2 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 84 + 4)) =
      some (.bitfield .W64 .UBFM (.gpr 8#5) (.gpr 8#5) 8 63))
    (hf3 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 84 + 8)) =
      some (.ldr .W32 .W32 false (.gpr 9#5) (.RegOffset (.gpr 13#5) (.gpr 9#5) .UXTX 2)))
    (hf4 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 (N + 84 + 12)) =
      some (.logicalShift .W32 .EOR (.gpr 9#5) (.gpr 9#5) (.gpr 8#5) .LSL 0))
    (hk : ∀ v, Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 (N + 100)) ps
      { r with x8 := v, x9 := (crcWord c w).setWidth 64 })) :
    Reach pl s0 X (mkS s0 m sp (pl.base + BitVec.ofNat 64 N) ps r) := by
  refine rounds9 hrun hT 7 N r h13 hf fun v => ?_
  refine last99 hrun hT (N + 84) _ h13 hf1 hf2 hf3 hf4 fun v' => ?_
  have := hk v'
  rw [show N + 84 + 16 = N + 100 by omega]
  rw [← crcWord_val, ← hx] at this
  exact this

end

theorem foldLast_eq (bs : List (BitVec 8)) (q : ℕ) (c : BitVec 32) (K : ℕ) :
    foldLast bs q c K =
      crcWord (crcWord (crcWord (crcWord (crcWord (0 ^^^ braids bs q c K 0)
        (wordLE bs (q + 40 * K + 8 * 0)) ^^^ braids bs q c K 1) (wordLE bs (q + 40 * K + 8 * 1)) ^^^
        braids bs q c K 2) (wordLE bs (q + 40 * K + 8 * 2)) ^^^ braids bs q c K 3)
        (wordLE bs (q + 40 * K + 8 * 3)) ^^^ braids bs q c K 4) (wordLE bs (q + 40 * K + 8 * 4)) := by
  rfl

theorem awc_add (x y : BitVec 64) : (AddWithCarry64 x y false).1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth]; omega

theorem bne_ofNat_zero (r : ℕ) (hr : r < 2 ^ 64) :
    ((BitVec.ofNat 64 r == 0#64) != true) = decide (r ≠ 0) := by
  by_cases h : r = 0
  · subst h; rfl
  · have : BitVec.ofNat 64 r ≠ 0#64 := by
      intro h'; have := congrArg BitVec.toNat h'
      rw [toNat_ofNat_lt r hr] at this; exact h this
    simp [this, h]

theorem xz (w : BitVec 64) (b : BitVec 32) :
    w ^^^ b.setWidth 64 = w ^^^ (0 ^^^ b).setWidth 64 := by simp

theorem xor3 (w : BitVec 64) (a b : BitVec 32) :
    w ^^^ b.setWidth 64 ^^^ a.setWidth 64 = w ^^^ (a ^^^ b).setWidth 64 := by
  rw [BitVec.setWidth_xor]; ac_rfl

set_option maxHeartbeats 4000000 in
theorem fold {pl : Placement} {s0 : State} {bs : List (BitVec 8)} {m : Memory} {ps : PState}
    {R : Regs} (hE : Env pl s0 bs m) (c : BitVec 32) (q K : ℕ) (hqK : q + 40 * (K + 1) ≤ bs.length)
    (h1 : R.x1 = s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 (q + 40 * K))
    (h2 : R.x2 = BitVec.ofNat 64 (bs.length - (q + 40 * (K + 1))))
    (h9 : R.x9 = (braids bs q c K 0).setWidth 64) (h19 : R.x19 = (braids bs q c K 1).setWidth 64)
    (h0 : R.x0 = (braids bs q c K 2).setWidth 64) (h18 : R.x18 = (braids bs q c K 3).setWidth 64)
    (h14 : R.x14 = (braids bs q c K 4).setWidth 64) (h13 : R.x13 = pl.ρ crcTabSym) :
    Reach pl s0 ((~~~ crcBytes (foldLast bs q c K) (bs.drop (q + 40 * (K + 1)))).setWidth 64)
      (mkS s0 m (spIn s0) (pl.base + 1076#64) ps R) := by
  have hP := hE.hP
  have hCL := hE.hCL
  have hrun := hE.hrun
  have hlen := hE.hlen
  have hT := hE.hT
  have rd : ∀ j, j < 5 → _ := fun j hj => ro_read64 hE.hbuf (q + 40 * K + 8 * j) (by omega)
  have r0 := rd 0 (by decide)
  have r1 := rd 1 (by decide)
  have r2 := rd 2 (by decide)
  have r3 := rd 3 (by decide)
  have r4 := rd 4 (by decide)
  generalize hA : s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 (q + 40 * K) = A at h1
  have ha : ∀ j, s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 (q + 40 * K + 8 * j) =
      A + BitVec.ofNat 64 (8 * j) := by
    intro j; rw [← hA, BitVec.add_assoc, ← BitVec.ofNat_add]
  rw [ha] at r0 r1 r2 r3 r4
  simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at r0 r1 r2 r3 r4
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19,
    x20, x21, x22, x23, x24, x25, x26, x27, x28, x30⟩ := R
  dsimp only at h1 h2 h9 h19 h0 h18 h14 h13
  subst h1 h2 h9 h19 h0 h18 h14 h13
  refine reach_step (stepM hrun (f_428 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, r3.1, r3.2, r4.1, r4.2, BitVec.add_assoc, BitVec.reduceAdd]
  refine reach_step (stepM hrun (f_42c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, r3.1, r3.2, r4.1, r4.2, BitVec.add_assoc, BitVec.reduceAdd]
  refine word98 (N := 1084) hrun hT _ rfl (0 ^^^ braids bs q c K 0)
    (wordLE bs (q + 40 * K + 8 * 0)) (xz _ _) (fun j hj => by interval_cases j; exacts [⟨f_430 hP hCL, f_434 hP hCL, f_438 hP hCL⟩, ⟨f_43c hP hCL, f_440 hP hCL, f_444 hP hCL⟩, ⟨f_448 hP hCL, f_44c hP hCL, f_450 hP hCL⟩, ⟨f_454 hP hCL, f_458 hP hCL, f_45c hP hCL⟩, ⟨f_460 hP hCL, f_464 hP hCL, f_468 hP hCL⟩, ⟨f_46c hP hCL, f_470 hP hCL, f_474 hP hCL⟩, ⟨f_478 hP hCL, f_47c hP hCL, f_480 hP hCL⟩])
    (f_484 hP hCL) (f_488 hP hCL) (f_48c hP hCL) (f_490 hP hCL) fun v => ?_
  refine reach_step (stepM hrun (f_494 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, r3.1, r3.2, r4.1, r4.2, BitVec.add_assoc, BitVec.reduceAdd]
  refine reach_step (stepM hrun (f_498 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, r3.1, r3.2, r4.1, r4.2, BitVec.add_assoc, BitVec.reduceAdd]
  refine word98 (N := 1192) hrun hT _ rfl _ (wordLE bs (q + 40 * K + 8 * 1)) (xor3 _ _ _) (fun j hj => by interval_cases j; exacts [⟨f_49c hP hCL, f_4a0 hP hCL, f_4a4 hP hCL⟩, ⟨f_4a8 hP hCL, f_4ac hP hCL, f_4b0 hP hCL⟩, ⟨f_4b4 hP hCL, f_4b8 hP hCL, f_4bc hP hCL⟩, ⟨f_4c0 hP hCL, f_4c4 hP hCL, f_4c8 hP hCL⟩, ⟨f_4cc hP hCL, f_4d0 hP hCL, f_4d4 hP hCL⟩, ⟨f_4d8 hP hCL, f_4dc hP hCL, f_4e0 hP hCL⟩, ⟨f_4e4 hP hCL, f_4e8 hP hCL, f_4ec hP hCL⟩])
    (f_4f0 hP hCL) (f_4f4 hP hCL) (f_4f8 hP hCL) (f_4fc hP hCL) fun v => ?_
  refine reach_step (stepM hrun (f_500 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, r3.1, r3.2, r4.1, r4.2, BitVec.add_assoc, BitVec.reduceAdd]
  refine reach_step (stepM hrun (f_504 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, r3.1, r3.2, r4.1, r4.2, BitVec.add_assoc, BitVec.reduceAdd]
  refine reach_step (stepM hrun (f_508 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, r3.1, r3.2, r4.1, r4.2, BitVec.add_assoc, BitVec.reduceAdd]
  refine reach_step (stepM hrun (f_50c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, r3.1, r3.2, r4.1, r4.2, BitVec.add_assoc, BitVec.reduceAdd]
  refine word108 (N := 1308) hrun hT _ rfl _ (wordLE bs (q + 40 * K + 8 * 2)) (xor3 _ _ _) (fun j hj => by interval_cases j; exacts [⟨f_510 hP hCL, f_514 hP hCL, f_518 hP hCL⟩, ⟨f_51c hP hCL, f_520 hP hCL, f_524 hP hCL⟩, ⟨f_528 hP hCL, f_52c hP hCL, f_530 hP hCL⟩, ⟨f_534 hP hCL, f_538 hP hCL, f_53c hP hCL⟩, ⟨f_540 hP hCL, f_544 hP hCL, f_548 hP hCL⟩, ⟨f_54c hP hCL, f_550 hP hCL, f_554 hP hCL⟩, ⟨f_558 hP hCL, f_55c hP hCL, f_560 hP hCL⟩])
    (f_564 hP hCL) (f_568 hP hCL) (f_56c hP hCL) (f_570 hP hCL) fun v => ?_
  refine reach_step (stepM hrun (f_574 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, r3.1, r3.2, r4.1, r4.2, BitVec.add_assoc, BitVec.reduceAdd]
  refine reach_step (stepM hrun (f_578 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, r3.1, r3.2, r4.1, r4.2, BitVec.add_assoc, BitVec.reduceAdd]
  refine reach_step (stepM hrun (f_57c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, r3.1, r3.2, r4.1, r4.2, BitVec.add_assoc, BitVec.reduceAdd]
  refine word98 (N := 1420) hrun hT _ rfl _ (wordLE bs (q + 40 * K + 8 * 3)) (xor3 _ _ _) (fun j hj => by interval_cases j; exacts [⟨f_580 hP hCL, f_584 hP hCL, f_588 hP hCL⟩, ⟨f_58c hP hCL, f_590 hP hCL, f_594 hP hCL⟩, ⟨f_598 hP hCL, f_59c hP hCL, f_5a0 hP hCL⟩, ⟨f_5a4 hP hCL, f_5a8 hP hCL, f_5ac hP hCL⟩, ⟨f_5b0 hP hCL, f_5b4 hP hCL, f_5b8 hP hCL⟩, ⟨f_5bc hP hCL, f_5c0 hP hCL, f_5c4 hP hCL⟩, ⟨f_5c8 hP hCL, f_5cc hP hCL, f_5d0 hP hCL⟩])
    (f_5d4 hP hCL) (f_5d8 hP hCL) (f_5dc hP hCL) (f_5e0 hP hCL) fun v => ?_
  refine reach_step (stepM hrun (f_5e4 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, r3.1, r3.2, r4.1, r4.2, BitVec.add_assoc, BitVec.reduceAdd]
  refine reach_step (stepM hrun (f_5e8 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, r0.1, r0.2, r1.1, r1.2, r2.1, r2.2, r3.1, r3.2, r4.1, r4.2, BitVec.add_assoc, BitVec.reduceAdd]
  refine word99 (N := 1528) hrun hT _ rfl _ (wordLE bs (q + 40 * K + 8 * 4)) (xor3 _ _ _) (fun j hj => by interval_cases j; exacts [⟨f_5ec hP hCL, f_5f0 hP hCL, f_5f4 hP hCL⟩, ⟨f_5f8 hP hCL, f_5fc hP hCL, f_600 hP hCL⟩, ⟨f_604 hP hCL, f_608 hP hCL, f_60c hP hCL⟩, ⟨f_610 hP hCL, f_614 hP hCL, f_618 hP hCL⟩, ⟨f_61c hP hCL, f_620 hP hCL, f_624 hP hCL⟩, ⟨f_628 hP hCL, f_62c hP hCL, f_630 hP hCL⟩, ⟨f_634 hP hCL, f_638 hP hCL, f_63c hP hCL⟩])
    (f_640 hP hCL) (f_644 hP hCL) (f_648 hP hCL) (f_64c hP hCL) fun v => ?_
  rw [← foldLast_eq]
  refine reach_step (stepM hrun (f_650 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd]
  refine reach_step (stepM hrun (f_654 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd, cond_CC, awc_add]
  have hr : (BitVec.ofNat 64 (bs.length - (q + 40 * (K + 1)))).toNat =
      bs.length - (q + 40 * (K + 1)) := toNat_ofNat_lt _ (by omega)
  have h40 : x1 + 40#64 = s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 (q + 40 * (K + 1)) := by
    rw [← hA, BitVec.add_assoc]; congr 1
    rw [show (40#64 : BitVec 64) = BitVec.ofNat 64 40 from rfl, ← BitVec.ofNat_add]; congr 1
  simp only [hr, h40, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  by_cases hlt : bs.length - (q + 40 * (K + 1)) < 8
  · simp only [hlt, decide_true, if_true]
    refine reach_step (stepM hrun (f_038 hP hCL)) ?_
    simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd,
      bne_ofNat_zero _ (show bs.length - (q + 40 * (K + 1)) < 2 ^ 64 by omega)]
    by_cases hz : bs.length - (q + 40 * (K + 1)) = 0
    · simp only [hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
      refine reach_step (stepM hrun (f_03c hP hCL)) ?_
      simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceAdd]
      rw [List.drop_eq_nil_of_le (by omega), crcBytes, List.foldl_nil]
      exact epi hP hCL hrun hE.hal hE.hF hE.hS _ rfl
    · simp only [hz, ne_eq, not_false_eq_true, decide_true, if_true]
      exact tail hE _ (q + 40 * (K + 1)) (bs.length - (q + 40 * (K + 1))) (by omega) (by omega)
        (by omega) rfl rfl rfl rfl
  · simp only [hlt, decide_false, Bool.false_eq_true, if_false]
    exact loop8 hE _ (q + 40 * (K + 1)) (by omega) rfl rfl rfl rfl

end ZlibCrc32.Crcz.PartFS

namespace ZlibCrc32.Crcz
alias fold := PartFS.fold
end ZlibCrc32.Crcz
end

section
/-! # Part BL: the braided loop of `crc32_z` (`0x1f4 .. 0x414`) -/

namespace ZlibCrc32.Crcz.PartBL

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

open Arm64 Arm64.Obj ZlibCrc32.Crcz

theorem len1 : zlibCrc32PlacedData1.length = 8192 := by decide +kernel

/-! ## Bit-vector helpers -/

theorem bf_8 (d x : BitVec 64) : evalBitfield .W64 .UBFM d x 8 15 = (x >>> 8) &&& 255#64 := by
  rfl
theorem bf_16 (d x : BitVec 64) : evalBitfield .W64 .UBFM d x 16 23 = (x >>> 16) &&& 255#64 := by
  rfl
theorem bf_32 (d x : BitVec 64) : evalBitfield .W64 .UBFM d x 32 39 = (x >>> 32) &&& 255#64 := by
  rfl
theorem bf_40 (d x : BitVec 64) : evalBitfield .W64 .UBFM d x 40 47 = (x >>> 40) &&& 255#64 := by
  rfl
theorem bf_48 (d x : BitVec 64) : evalBitfield .W64 .UBFM d x 48 55 = (x >>> 48) &&& 255#64 := by
  rfl
theorem bf_56 (d x : BitVec 64) : evalBitfield .W64 .UBFM d x 56 63 = x >>> 56 := by
  rfl
theorem bf_24w (d x : BitVec 64) :
    ((evalBitfield .W32 .UBFM d ((x.setWidth 32).setWidth 64) 24 31).setWidth 32).setWidth 64 =
      (x >>> 24) &&& 255#64 := by
  have h : evalBitfield .W32 .UBFM d ((x.setWidth 32).setWidth 64) 24 31 =
      ((((((x.setWidth 32).setWidth 64).setWidth 32).setWidth 64) >>> 24).setWidth 32).setWidth 64 :=
    rfl
  rw [h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_and, Nat.shiftRight_eq_div_pow]
  rw [show (255#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

/-! ## The table load `ldr wT, [xB, xI, lsl #2]` -/

theorem tz (a : BitVec 32) : (a.setWidth 64).setWidth 32 = a := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]

theorem ldrT {pl : Placement} {s0 : State} {m : Memory} {sp pc : BitVec 64} {ps : PState}
    {r : Regs} {X : BitVec 64} {rt rb ri : BitVec 5} {U : BitVec 64} (k' : ℕ)
    (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem m pc =
      some (.ldr .W32 .W32 false (.gpr rt) (.RegOffset (.gpr rb) (.gpr ri) .UXTX 2)))
    (hU : RoBytes m U zlibCrc32PlacedData1) (hk : k' < 8)
    (hb : (mkS s0 m sp pc ps r).readReg64 (.gpr rb) = U + BitVec.ofNat 64 (1024 * k'))
    (hi : ((mkS s0 m sp pc ps r).readReg64 (.gpr ri)).toNat < 256)
    (h : Reach pl s0 X (((mkS s0 m sp pc ps r).writeReg64 (.gpr rt)
      ((TB k' ((mkS s0 m sp pc ps r).readReg64 (.gpr ri)).toNat).setWidth 64)).advancePC)) :
    Reach pl s0 X (mkS s0 m sp pc ps r) := by
  refine reach_step (stepM hrun hf) ?_
  have hm : (mkS s0 m sp pc ps r).mem = m := rfl
  generalize mkS s0 m sp pc ps r = s at hb hi h hm ⊢
  subst hm
  generalize hidef : s.readReg64 (.gpr ri) = i at hi h
  obtain ⟨hc, hv⟩ := ro_read32 hU (256 * k' + i.toNat) (by rw [len1]; omega)
  have haddr : s.readReg64 (.gpr rb) + extendVal .W64 i .UXTX 2 =
      U + BitVec.ofNat 64 (4 * (256 * k' + i.toNat)) := by
    rw [hb]; apply BitVec.eq_of_toNat_eq
    simp only [extendVal, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]
    omega
  simp only [ex_ldr, execLdr, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned,
    evalAddrMode, hidef, haddr, hc, Bool.not_true, Bool.false_eq_true, if_false, MemWidth.bytes,
    Memory.readSized, hv, State.writeReg]
  rw [show (BitVec.truncate 32 (BitVec.zeroExtend 64 (word32 zlibCrc32PlacedData1
    (256 * k' + i.toNat)))) = TB k' i.toNat from tz _]
  exact h

/-! ## Small rewriting lemmas for the loop body -/

theorem xor_sw (a b : BitVec 32) : a.setWidth 64 ^^^ b.setWidth 64 = (a ^^^ b).setWidth 64 := by
  rw [BitVec.setWidth_xor]

theorem awc_add (x y : BitVec 64) : (AddWithCarry64 x y false).1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth]; omega

theorem awc_sub (x y : BitVec 64) : (AddWithCarry64 x (~~~y) true).1 = x - y := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_sub]
  omega

theorem awc_z (x y : BitVec 64) : (AddWithCarry64 x (~~~y) true).2.z = decide (x.toNat = y.toNat) := by
  simp only [AddWithCarry64, if_true]
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [← BitVec.toNat_inj]
  simp [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_not]
  omega

theorem idx_and (x : BitVec 64) : (x &&& 255#64).toNat < 256 := by
  rw [BitVec.toNat_and]; exact lt_of_le_of_lt Nat.and_le_right (by decide)

theorem idx_56 (x : BitVec 64) : (x >>> 56).toNat < 256 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; have := x.isLt; omega

theorem toNat_and255 (x : BitVec 64) : (x &&& 255#64).toNat = x.toNat % 256 := by
  rw [BitVec.toNat_and, show (255#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

theorem hi_shift (c : BitVec 32) (w : BitVec 64) (i : ℕ) (hi : 32 ≤ i) :
    (c.setWidth 64 ^^^ w) >>> i = w >>> i := by
  rw [BitVec.ushiftRight_xor_distrib]
  have : c.setWidth 64 >>> i = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_setWidth, Nat.shiftRight_eq_div_pow,
      BitVec.toNat_ofNat]
    have h1 := c.isLt
    have h2 : 2 ^ 32 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hi
    rw [Nat.div_eq_of_lt (by omega)]
  rw [this, BitVec.zero_xor]

theorem braidWord_alt (c : BitVec 32) (w : BitVec 64) :
    braidWord (c.setWidth 64 ^^^ w) =
      TB 0 ((w ^^^ c.setWidth 64) &&& 255#64).toNat ^^^
      TB 1 ((w ^^^ c.setWidth 64) >>> 8 &&& 255#64).toNat ^^^
      TB 2 ((w ^^^ c.setWidth 64) >>> 16 &&& 255#64).toNat ^^^
      TB 3 ((w ^^^ c.setWidth 64) >>> 24 &&& 255#64).toNat ^^^
      TB 4 (w >>> 32 &&& 255#64).toNat ^^^ TB 5 (w >>> 40 &&& 255#64).toNat ^^^
      TB 6 (w >>> 48 &&& 255#64).toNat ^^^ TB 7 (w >>> 56).toNat := by
  rw [← hi_shift c w 32 (by omega), ← hi_shift c w 40 (by omega), ← hi_shift c w 48 (by omega),
    ← hi_shift c w 56 (by omega), BitVec.xor_comm w]
  simp only [braidWord, toNat_and255]
  rw [Nat.mod_eq_of_lt (idx_56 _)]

set_option maxHeartbeats 4000000 in
theorem body {pl : Placement} {s0 : State} {m : Memory} {sp : BitVec 64} {ps : PState}
    {X : BitVec 64} (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded m)
    (hrun : s0.status = .Running) {U A w0 w1 w2 w3 w4 : BitVec 64} {c0 c1 c2 c3 c4 : BitVec 32}
    (hU : RoBytes m U zlibCrc32PlacedData1)
    (hcr0 : m.canRead A 8 = true) (hcr8 : m.canRead (A + 8#64) 8 = true)
    (hcr16 : m.canRead (A + 16#64) 8 = true) (hcr24 : m.canRead (A + 24#64) 8 = true)
    (hcr32 : m.canRead (A + 32#64) 8 = true)
    (hrd0 : m.read64 A = w0) (hrd8 : m.read64 (A + 8#64) = w1) (hrd16 : m.read64 (A + 16#64) = w2)
    (hrd24 : m.read64 (A + 24#64) = w3) (hrd32 : m.read64 (A + 32#64) = w4)
    (r : Regs) (h17 : r.x17 = A) (h12 : r.x12 = U) (h13 : r.x13 = U + 0x1400#64)
    (h15 : r.x15 = U + 0x1800#64) (h16 : r.x16 = U + 0x1c00#64)
    (h9 : r.x9 = c0.setWidth 64) (h19 : r.x19 = c1.setWidth 64) (h0 : r.x0 = c2.setWidth 64)
    (h18 : r.x18 = c3.setWidth 64) (h14 : r.x14 = c4.setWidth 64)
    (hk : ∀ r' : Regs, r'.x1 = r.x1 → r'.x2 = r.x2 → r'.x11 = r.x11 - 1#64 → r'.x17 = A + 40#64 →
      r'.x12 = U → r'.x13 = U + 0x1400#64 → r'.x15 = U + 0x1800#64 → r'.x16 = U + 0x1c00#64 →
      r'.x9 = (braidWord (c0.setWidth 64 ^^^ w0)).setWidth 64 →
      r'.x19 = (braidWord (c1.setWidth 64 ^^^ w1)).setWidth 64 →
      r'.x0 = (braidWord (c2.setWidth 64 ^^^ w2)).setWidth 64 →
      r'.x18 = (braidWord (c3.setWidth 64 ^^^ w3)).setWidth 64 →
      r'.x14 = (braidWord (c4.setWidth 64 ^^^ w4)).setWidth 64 →
      Reach pl s0 X (mkS s0 m sp (pl.base + 1028#64) (AddWithCarry64 r.x11 (~~~1#64) true).2 r')) :
    Reach pl s0 X (mkS s0 m sp (pl.base + 512#64) ps r) := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19,
    x20, x21, x22, x23, x24, x25, x26, x27, x28, x30⟩ := r
  dsimp only at h17 h12 h13 h15 h16 h9 h19 h0 h18 h14 hk
  subst h17 h12 h13 h15 h16 h9 h19 h0 h18 h14
  refine reach_step (stepM hrun (f_1f4 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_1f8 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_1fc hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_200 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_204 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_208 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_20c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_210 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_214 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_218 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_21c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_220 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 0 hrun (f_224 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> exact (BitVec.add_zero _).symm) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_228 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_22c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_230 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_234 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_238 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 0 hrun (f_23c hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> exact (BitVec.add_zero _).symm) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 0 hrun (f_240 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> exact (BitVec.add_zero _).symm) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 1 hrun (f_244 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 1 hrun (f_248 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_24c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_250 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_254 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_258 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_25c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 0 hrun (f_260 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> exact (BitVec.add_zero _).symm) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 0 hrun (f_264 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> exact (BitVec.add_zero _).symm) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_268 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_26c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 1 hrun (f_270 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 1 hrun (f_274 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 1 hrun (f_278 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_27c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_280 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_284 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_288 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_28c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_290 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_294 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_298 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_29c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_2a0 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 2 hrun (f_2a4 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 2 hrun (f_2a8 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_2ac hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 3 hrun (f_2b0 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 3 hrun (f_2b4 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_2b8 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 2 hrun (f_2bc hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 3 hrun (f_2c0 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 2 hrun (f_2c4 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_2c8 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_2cc hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_2d0 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_2d4 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 3 hrun (f_2d8 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_2dc hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_2e0 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_2e4 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_2e8 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 4 hrun (f_2ec hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 4 hrun (f_2f0 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_2f4 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_2f8 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 2 hrun (f_2fc hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_300 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 3 hrun (f_304 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_308 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_30c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 4 hrun (f_310 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_314 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 4 hrun (f_318 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_31c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_320 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_324 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_328 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 4 hrun (f_32c hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_330 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_334 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_338 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_33c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_340 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_344 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_348 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_34c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_350 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 5 hrun (f_354 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_358 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 5 hrun (f_35c hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 5 hrun (f_360 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_364 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 6 hrun (f_368 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_36c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_370 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 6 hrun (f_374 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_378 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_37c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_380 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_384 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_388 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_38c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 6 hrun (f_390 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_394 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_398 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_39c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 5 hrun (f_3a0 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 5 hrun (f_3a4 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 6 hrun (f_3a8 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_3ac hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 6 hrun (f_3b0 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 7 hrun (f_3b4 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 7 hrun (f_3b8 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 7 hrun (f_3bc hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 7 hrun (f_3c0 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine ldrT 7 hrun (f_3c4 hP hCL) hU (by decide) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> rfl) (by simp only [rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30] <;> first | exact idx_and _ | exact idx_56 _) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_3c8 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_3cc hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_3d0 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_3d4 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_3d8 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_3dc hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_3e0 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_3e4 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_3e8 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_3ec hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_3f0 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hrun (f_3f4 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, evalAddSub, ex_bitfield, execBitfield, bf_8, bf_16, bf_32, bf_40, bf_48, bf_56, bf_24w, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, tz, xor_sw, awc_add, awc_sub, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, hcr0, hcr8, hcr16, hcr24, hcr32, hrd0, hrd8, hrd16, hrd24, hrd32, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  exact hk _ rfl rfl rfl rfl rfl rfl rfl rfl (by rw [braidWord_alt]; ac_rfl)
    (by rw [braidWord_alt]; ac_rfl) (by rw [braidWord_alt]; ac_rfl) (by rw [braidWord_alt]; ac_rfl)
    (by rw [braidWord_alt]; ac_rfl)

/-! ## The exit path `0x3fc .. 0x414`, then the fold -/

set_option maxHeartbeats 1000000 in
theorem exitPath {pl : Placement} {s0 : State} {bs : List (BitVec 8)} {m : Memory}
    (hE : Env pl s0 bs m) (c : BitVec 32) (q K : ℕ) (ps : PState) (r : Regs)
    (hslot : m.read64 (slot s0 1) = BitVec.ofNat 64 (K + 1))
    (hqK : q + 40 * (K + 1) ≤ bs.length)
    (h1 : r.x1 = s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 q)
    (h2 : r.x2 = BitVec.ofNat 64 (bs.length - (q + 40 * (K + 1))))
    (h9 : r.x9 = (braids bs q c K 0).setWidth 64) (h19 : r.x19 = (braids bs q c K 1).setWidth 64)
    (h0 : r.x0 = (braids bs q c K 2).setWidth 64) (h18 : r.x18 = (braids bs q c K 3).setWidth 64)
    (h14 : r.x14 = (braids bs q c K 4).setWidth 64) :
    Reach pl s0 ((~~~ crcBytes (foldLast bs q c K) (bs.drop (q + 40 * (K + 1)))).setWidth 64)
      (mkS s0 m (spIn s0) (pl.base + 1032#64) ps r) := by
  have hal' : (spIn s0 &&& 15#64 == 0#64) = true := aligned_add s0.sp _ (by decide) hE.hal
  have cr1 := frameOk_canRead hE.hF 1 (by decide)
  have hsl := hslot
  rw [slot_eq s0 _ (by decide)] at cr1 hsl
  simp only [Nat.reduceMul, Nat.reduceAdd] at cr1 hsl
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19,
    x20, x21, x22, x23, x24, x25, x26, x27, x28, x30⟩ := r
  dsimp only at h1 h2 h9 h19 h0 h18 h14
  subst h1 h2 h9 h19 h0 h18 h14
  refine reach_step (stepM hE.hrun (f_3fc hE.hP hE.hCL)) ?_
  simp only [ex_ldr, execLdr, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_addSubImm, execAddSubImm, evalAddSub, ex_b, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned, mkS_sp, hal', evalAddrMode, rd_sp, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPC, mkS_pc, if_true, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, awc_sub, Bool.not_true, Bool.false_eq_true, if_false, cr1, hsl, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hE.hrun (f_400 hE.hP hE.hCL)) ?_
  simp only [ex_ldr, execLdr, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_addSubImm, execAddSubImm, evalAddSub, ex_b, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned, mkS_sp, hal', evalAddrMode, rd_sp, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPC, mkS_pc, if_true, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, awc_sub, Bool.not_true, Bool.false_eq_true, if_false, cr1, hsl, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_steps (reloc1040 hE.hP hE.hCL hE.hrun _) ?_
  refine reach_step (stepM hE.hrun (f_40c hE.hP hE.hCL)) ?_
  simp only [ex_ldr, execLdr, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_addSubImm, execAddSubImm, evalAddSub, ex_b, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned, mkS_sp, hal', evalAddrMode, rd_sp, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPC, mkS_pc, if_true, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, awc_sub, Bool.not_true, Bool.false_eq_true, if_false, cr1, hsl, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hE.hrun (f_410 hE.hP hE.hCL)) ?_
  simp only [ex_ldr, execLdr, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_addSubImm, execAddSubImm, evalAddSub, ex_b, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned, mkS_sp, hal', evalAddrMode, rd_sp, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPC, mkS_pc, if_true, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, awc_sub, Bool.not_true, Bool.false_eq_true, if_false, cr1, hsl, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine reach_step (stepM hE.hrun (f_414 hE.hP hE.hCL)) ?_
  simp only [ex_ldr, execLdr, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_addSubImm, execAddSubImm, evalAddSub, ex_b, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned, mkS_sp, hal', evalAddrMode, rd_sp, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPC, mkS_pc, if_true, BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, mkS_mem, Memory.readSized, MemWidth.bytes, BitVec.add_assoc, BitVec.reduceAdd, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, awc_sub, Bool.not_true, Bool.false_eq_true, if_false, cr1, hsl, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30]
  refine fold hE c q K hqK ?_ rfl rfl rfl rfl rfl rfl rfl
  dsimp only
  bv_omega

/-! ## The loop -/

theorem cond_ne (K k : ℕ) (hK : K - k < 2 ^ 64) :
    ConditionHolds .NE (AddWithCarry64 (BitVec.ofNat 64 (K - k)) (~~~1#64) true).2 =
      decide (K - k ≠ 1) := by
  simp only [ConditionHolds, awc_z, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hK]
  by_cases h : K - k = 1 <;> simp [h]

theorem loop_aux {pl : Placement} {s0 : State} {bs : List (BitVec 8)} {m : Memory}
    (hE : Env pl s0 bs m) (c : BitVec 32) (q K : ℕ)
    (hslot : m.read64 (slot s0 1) = BitVec.ofNat 64 (K + 1))
    (hqK : q + 40 * (K + 1) ≤ bs.length) (n : ℕ) :
    ∀ (k : ℕ) (ps : PState) (R : Regs), n = K - k → k < K →
    R.x11 = BitVec.ofNat 64 (K - k) →
    R.x17 = s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 (q + 40 * k) →
    R.x1 = s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 q →
    R.x2 = BitVec.ofNat 64 (bs.length - (q + 40 * (K + 1))) →
    R.x9 = (braids bs q c k 0).setWidth 64 → R.x19 = (braids bs q c k 1).setWidth 64 →
    R.x0 = (braids bs q c k 2).setWidth 64 → R.x18 = (braids bs q c k 3).setWidth 64 →
    R.x14 = (braids bs q c k 4).setWidth 64 →
    R.x12 = pl.ρ braidTabSym → R.x13 = pl.ρ braidTabSym + 0x1400#64 →
    R.x15 = pl.ρ braidTabSym + 0x1800#64 → R.x16 = pl.ρ braidTabSym + 0x1c00#64 →
    Reach pl s0 ((~~~ crcBytes (foldLast bs q c K) (bs.drop (q + 40 * (K + 1)))).setWidth 64)
      (mkS s0 m (spIn s0) (pl.base + 512#64) ps R) := by
  induction n with
  | zero => intro k ps R hn hk; omega
  | succ n ih =>
    intro k ps R hn hk h11 h17 h1 h2 h9 h19 h0 h18 h14 h12 h13 h15 h16
    have hlen := hE.hlen
    have ha : ∀ j, s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 (q + 40 * k) + BitVec.ofNat 64 (8 * j) =
        s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 (q + 40 * k + 8 * j) := fun j => by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    have rd : ∀ j, j < 5 → _ := fun j hj => ro_read64 hE.hbuf (q + 40 * k + 8 * j) (by omega)
    have r0 := rd 0 (by decide); have r1 := rd 1 (by decide); have r2 := rd 2 (by decide)
    have r3 := rd 3 (by decide); have r4 := rd 4 (by decide)
    rw [← ha] at r1 r2 r3 r4
    refine body hE.hP hE.hCL hE.hrun hE.hU r0.1 r1.1 r2.1 r3.1 r4.1 r0.2 r1.2 r2.2 r3.2 r4.2
      R h17 h12 h13 h15 h16 h9 h19 h0 h18 h14 ?_
    intro r' h1' h2' h11' h17' h12' h13' h15' h16' h9' h19' h0' h18' h14'
    refine reach_step (stepM hE.hrun (f_3f8 hE.hP hE.hCL)) ?_
    simp only [ex_bCond, mkS_pstate, h11, cond_ne K k (by omega)]
    by_cases hlast : K - k = 1
    · simp only [hlast, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false,
        mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd]
      have hkK : K = k + 1 := by omega
      subst hkK
      exact exitPath hE c q (k + 1) _ r' hslot hqK (h1'.trans h1) (h2'.trans h2) h9' h19' h0' h18' h14'
    · simp only [hlast, ne_eq, not_false_eq_true, decide_true, if_true, mkS_setPC, mkS_pc,
        BitVec.add_assoc, BitVec.reduceAdd]
      refine ih (k + 1) _ r' (by omega) (by omega) ?_ ?_ (h1'.trans h1) (h2'.trans h2) h9' h19' h0'
        h18' h14' h12' h13' h15' h16'
      · rw [h11', h11]; bv_omega
      · rw [h17']; bv_omega

theorem braidLoop {pl : Placement} {s0 : State} {bs : List (BitVec 8)} {m : Memory} {ps : PState}
    {R : Regs} (hE : Env pl s0 bs m) (c : BitVec 32) (q K k : ℕ)
    (hslot : m.read64 (slot s0 1) = BitVec.ofNat 64 (K + 1))
    (hk : k < K) (hqK : q + 40 * (K + 1) ≤ bs.length)
    (h11 : R.x11 = BitVec.ofNat 64 (K - k))
    (h17 : R.x17 = s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 (q + 40 * k))
    (h1 : R.x1 = s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 q)
    (h2 : R.x2 = BitVec.ofNat 64 (bs.length - (q + 40 * (K + 1))))
    (h9 : R.x9 = (braids bs q c k 0).setWidth 64) (h19 : R.x19 = (braids bs q c k 1).setWidth 64)
    (h0 : R.x0 = (braids bs q c k 2).setWidth 64) (h18 : R.x18 = (braids bs q c k 3).setWidth 64)
    (h14 : R.x14 = (braids bs q c k 4).setWidth 64)
    (h12 : R.x12 = pl.ρ braidTabSym) (h13 : R.x13 = pl.ρ braidTabSym + 0x1400#64)
    (h15 : R.x15 = pl.ρ braidTabSym + 0x1800#64) (h16 : R.x16 = pl.ρ braidTabSym + 0x1c00#64) :
    Reach pl s0 ((~~~ crcBytes (foldLast bs q c K) (bs.drop (q + 40 * (K + 1)))).setWidth 64)
      (mkS s0 m (spIn s0) (pl.base + 512#64) ps R) :=
  loop_aux hE c q K hslot hqK (K - k) k ps R rfl hk h11 h17 h1 h2 h9 h19 h0 h18 h14 h12 h13 h15 h16


end ZlibCrc32.Crcz.PartBL

namespace ZlibCrc32.Crcz
alias braidLoop := PartBL.braidLoop
end ZlibCrc32.Crcz
end

section
/-! # Part FS: the fold of the last braided block (`0x428 .. 0x654`) and the block split
(`0x19c .. 0x1f0`, `0x418 .. 0x424`) of `crc32_z` -/

namespace ZlibCrc32.Crcz.PartFS

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

open Arm64 Arm64.Obj ZlibCrc32.Crcz

theorem bf_lsr5 (d x : BitVec 64) : evalBitfield .W64 .UBFM d x 5 63 = x >>> 5 := by rfl

theorem a1 (x : BitVec 64) : (BitVec.zeroExtend 128 x).toNat = x.toNat := by
  rw [BitVec.zeroExtend_eq_setWidth, BitVec.toNat_setWidth]; omega

theorem a2 (y : BitVec 128) : (y >>> 64).toNat = y.toNat / 2 ^ 64 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem a3 (y : BitVec 128) : (BitVec.truncate 64 y).toNat = y.toNat % 2 ^ 64 := by
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]

theorem a4 (x : BitVec 64) : (BitVec.zeroExtend 128 x * 14757395258967641293#128).toNat = (x.toNat * 14757395258967641293) % 2 ^ 128 := by
  rw [BitVec.toNat_mul, a1]; rfl

theorem umulh_div (L : ℕ) (hL : L < 2 ^ 64) :
    BitVec.truncate 64 ((BitVec.zeroExtend 128 (BitVec.ofNat 64 L) * 14757395258967641293#128) >>> 64)
      >>> 5 = BitVec.ofNat 64 (L / 40) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (L * 14757395258967641293) / 2 ^ 64 / 32 = L / 40 := by omega
  have h3 : L * 14757395258967641293 % 2 ^ 128 = L * 14757395258967641293 := Nat.mod_eq_of_lt (by omega)
  have h4 : L * 14757395258967641293 / 2 ^ 64 % 2 ^ 64 = L * 14757395258967641293 / 2 ^ 64 :=
    Nat.mod_eq_of_lt (by omega)
  have h5 : L / 40 % 2 ^ 64 = L / 40 := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, a3, a2, a4, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hL, h3, h4, h5]
  exact h1

theorem madd40 (L : ℕ) (hL : L < 2 ^ 64) :
    BitVec.ofNat 64 L + BitVec.ofNat 64 (L / 40) * ~~~39#64 = BitVec.ofNat 64 (L % 40) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hb' : L / 40 < 2 ^ 64 := by omega
  have h40 : L % 40 < 2 ^ 64 := by omega
  have e1 : L = 40 * (L / 40) + L % 40 := by omega
  generalize L / 40 = b at *
  have e : (2 ^ 64 - 1 - 39 % 2 ^ 64 : ℕ) = 2 ^ 64 - 40 := by norm_num
  rw [Nat.mod_eq_of_lt hL, Nat.mod_eq_of_lt hb', e, Nat.mod_eq_of_lt h40, Nat.add_mod_mod]
  have : L + b * (2 ^ 64 - 40) = L % 40 + 2 ^ 64 * b := by rw [Nat.mul_sub]; omega
  rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h40]

theorem sub1 (n : ℕ) (h1 : 1 ≤ n) (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n - 1#64 = BitVec.ofNat 64 (n - 1 - 0) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem ro_tr {s0 : State} {m m' : Memory} {a : BitVec 64} {bs : List (BitVec 8)}
    (hc : ∀ x, ¬ InRegion (s0.sp - 96#64) 96 x → m'.cells x = m.cells x)
    (hO : ∀ i, i < bs.length → ¬ InRegion (s0.sp - 96#64) 96 (a + BitVec.ofNat 64 i))
    (h : RoBytes m a bs) : RoBytes m' a bs := by
  intro i hi
  have e := hc _ (hO i hi)
  obtain ⟨h1, h2, h3⟩ := h i hi
  refine ⟨?_, ?_, ?_⟩
  · rw [← h1]; unfold Memory.read8; rw [e]
  · rw [← h2]; unfold Memory.perm; rw [e]
  · rw [← h3]; unfold Memory.isLazyFree; rw [e]

/-- The environment survives the spill to frame slot 1. -/
theorem env_write1 {pl : Placement} {s0 : State} {bs : List (BitVec 8)} {m : Memory}
    (hE : Env pl s0 bs m) (v : BitVec 64) : Env pl s0 bs (m.write64 (slot s0 1) v) := by
  let s0' : State := { s0 with mem := m }
  have hF' : FrameOk s0' m := fun a =>
    ⟨fun _ => rfl, fun h => by
      obtain ⟨a1, a2, _⟩ := (hE.hF a).2 h
      exact ⟨a1, a2, rfl⟩⟩
  have hF'' := (frameOk_write64 (s0 := s0') hF' 1 (by decide) v).2
  have hc : ∀ a, ¬ InRegion (s0.sp - 96#64) 96 a →
      (m.write64 (slot s0 1) v).cells a = m.cells a := fun a h => (hF'' a).1 h
  obtain ⟨s0_, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := hE.hS
  exact
    { hP := hE.hP
      hCL := codeLoaded_of_frame (s0 := s0') hF' hF'' hE.hCL
      hrun := hE.hrun
      hal := hE.hal
      hF := (frameOk_write64 hE.hF 1 (by decide) v).2
      hS := ⟨by rw [read64_write64_slot 0 1 (by decide) (by decide) (by decide)]; exact s0_,
        by rw [read64_write64_slot 2 1 (by decide) (by decide) (by decide)]; exact s2,
        by rw [read64_write64_slot 3 1 (by decide) (by decide) (by decide)]; exact s3,
        by rw [read64_write64_slot 4 1 (by decide) (by decide) (by decide)]; exact s4,
        by rw [read64_write64_slot 5 1 (by decide) (by decide) (by decide)]; exact s5,
        by rw [read64_write64_slot 6 1 (by decide) (by decide) (by decide)]; exact s6,
        by rw [read64_write64_slot 7 1 (by decide) (by decide) (by decide)]; exact s7,
        by rw [read64_write64_slot 8 1 (by decide) (by decide) (by decide)]; exact s8,
        by rw [read64_write64_slot 9 1 (by decide) (by decide) (by decide)]; exact s9,
        by rw [read64_write64_slot 10 1 (by decide) (by decide) (by decide)]; exact s10,
        by rw [read64_write64_slot 11 1 (by decide) (by decide) (by decide)]; exact s11⟩
      hbuf := ro_tr hc hE.hbufO hE.hbuf
      hT := ro_tr hc hE.hTO hE.hT
      hU := ro_tr hc hE.hUO hE.hU
      hlen := hE.hlen
      hbufO := hE.hbufO
      hTO := hE.hTO
      hUO := hE.hUO }

theorem setup {pl : Placement} {s0 : State} {bs : List (BitVec 8)} {m : Memory} {ps : PState}
    {R : Regs} (hE : Env pl s0 bs m) (c : BitVec 32) (q : ℕ) (hq : q + 40 ≤ bs.length)
    (h1 : R.x1 = s0.readReg64 (.gpr 1#5) + BitVec.ofNat 64 q)
    (h2 : R.x2 = BitVec.ofNat 64 (bs.length - q)) (h9 : R.x9 = c.setWidth 64)
    (h13 : R.x13 = pl.ρ crcTabSym) :
    Reach pl s0 ((~~~ crcBytes (foldLast bs q c ((bs.length - q) / 40 - 1))
        (bs.drop (q + 40 * ((bs.length - q) / 40 - 1 + 1)))).setWidth 64)
      (mkS s0 m (spIn s0) (pl.base + 424#64) ps R) := by
  have hP := hE.hP
  have hCL := hE.hCL
  have hrun := hE.hrun
  have hlen := hE.hlen
  have hal' : (spIn s0 &&& 15#64 == 0#64) = true := aligned_add s0.sp _ (by decide) hE.hal
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16, x17, x18, x19,
    x20, x21, x22, x23, x24, x25, x26, x27, x28, x30⟩ := R
  dsimp only at h1 h2 h9 h13
  subst h1 h2 h9 h13
  refine reach_step (stepM hrun (f_19c hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd]
  refine reach_step (stepM hrun (f_1a0 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd]
  refine reach_step (stepM hrun (f_1a4 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd]
  rw [show (0#64 ||| 14757395258967641292#64) &&& ~~~65535#64 ||| 52429#64 = 14757395258967641293#64
    by decide]
  refine reach_step (stepM hrun (f_1a8 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd]
  refine reach_step (stepM hrun (f_1ac hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd]
  rw [bf_lsr5, umulh_div _ (by omega)]
  refine reach_step (stepM hrun (f_1b0 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd]
  rw [madd40 _ (by omega)]
  refine reach_step (stepM hrun (f_1b4 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd]
  refine reach_step (stepM hrun (f_1b8 hP hCL)) ?_
  simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, awc_fst, cond_EQ,
    toNat_ofNat_lt _ (show (bs.length - q) / 40 < 2 ^ 64 by omega), BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod]
  by_cases hb : (bs.length - q) / 40 = 1
  · simp only [hb, decide_true, if_true, Nat.reduceSub, Nat.reduceAdd, Nat.reduceMul]
    refine reach_step (stepM hrun (f_418 hP hCL)) ?_
    simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_or, BitVec.reduceOr, awc_add,
      BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth]
    refine reach_step (stepM hrun (f_41c hP hCL)) ?_
    simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_or, BitVec.reduceOr, awc_add,
      BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth]
    refine reach_step (stepM hrun (f_420 hP hCL)) ?_
    simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_or, BitVec.reduceOr, awc_add,
      BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth]
    refine reach_step (stepM hrun (f_424 hP hCL)) ?_
    simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_or, BitVec.reduceOr, awc_add,
      BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth]
    exact fold hE c q 0 (by omega) (by simp) (congrArg (BitVec.ofNat 64) (by omega)) (by simp [braids])
      (by simp [braids]) (by simp [braids]) (by simp [braids]) (by simp [braids]) rfl
  · simp only [hb, decide_false, Bool.false_eq_true, if_false]
    refine reach_steps (reloc456 hP hCL hrun _) ?_
    refine reach_step (stepM hrun (f_1c4 hP hCL)) ?_
    simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_or, BitVec.reduceOr, awc_add,
      BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth]
    refine reach_step (stepM hrun (f_1c8 hP hCL)) ?_
    simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_or, BitVec.reduceOr, awc_add,
      BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth]
    refine reach_step (stepM hrun (f_1cc hP hCL)) ?_
    simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_or, BitVec.reduceOr, awc_add,
      BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth]
    refine reach_step (stepM hrun (f_1d0 hP hCL)) ?_
    simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_or, BitVec.reduceOr, awc_add,
      BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth]
    refine reach_step (stepM hrun (f_1d4 hP hCL)) ?_
    simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_or, BitVec.reduceOr, awc_add,
      BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth]
    refine reach_step (stepM hrun (f_1d8 hP hCL)) ?_
    simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_or, BitVec.reduceOr, awc_add,
      BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth]
    refine reach_step (stepM hrun (f_1dc hP hCL)) ?_
    simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_or, BitVec.reduceOr, awc_add,
      BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth]
    refine reach_step (stepM hrun (f_1e0 hP hCL)) ?_
    simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_or, BitVec.reduceOr, awc_add,
      BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth]
    refine reach_step (stepM hrun (f_1e4 hP hCL)) ?_
    simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_or, BitVec.reduceOr, awc_add,
      BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth]
    refine reach_step (stepM hrun (f_1e8 hP hCL)) ?_
    simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_or, BitVec.reduceOr, awc_add,
      BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth]
    refine reach_step (stepM hrun (f_1ec hP hCL)) ?_
    simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, BitVec.zero_or, BitVec.reduceOr, awc_add,
      BitVec.truncate_eq_setWidth, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth]
    have hsl : slot s0 1 = s0.sp + 18446744073709551528#64 := by
      rw [slot_eq s0 1 (by decide)]
    have hcw := (frameOk_write64 hE.hF 1 (by decide) (BitVec.ofNat 64 ((bs.length - q) / 40))).1
    rw [hsl] at hcw
    refine reach_step (stepM hrun (f_1f0 hP hCL)) ?_
    simp only [ex_ldp, execLdp, ex_ldr, execLdr, ex_str, execStr, ex_logicalImm, execLogicalImm, ex_logicalShift, execLogicalShift, evalLogical, ex_addSubImm, execAddSubImm, ex_addSubShift, execAddSubShift, evalAddSub, ex_bitfield, execBitfield, ex_moveWide, execMoveWide, ex_dataProc3, execDataProc3, ex_b, ex_bCond, ex_cbz, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, shiftVal, shift32, shift64, State.writeReg, State.readReg, State.readReg32, mkS_advancePC, mkS_setPState, mkS_setPC, mkS_setMem, mkS_mem, mkS_pc, mkS_pstate, Memory.readSized, MemWidth.bytes, BitVec.add_zero, Nat.zero_mod, BitVec.shiftLeft_zero, BitVec.reduceSetWidth, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft, Bool.not_true, Bool.false_eq_true, if_false, if_true, Bool.and_self, Bool.and_true, rd_xzr, wr_xzr, rd_sp, rd_x0, rd_x1, rd_x2, rd_x3, rd_x4, rd_x5, rd_x6, rd_x7, rd_x8, rd_x9, rd_x10, rd_x11, rd_x12, rd_x13, rd_x14, rd_x15, rd_x16, rd_x17, rd_x18, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27, rd_x28, rd_x30, wr_x0, wr_x1, wr_x2, wr_x3, wr_x4, wr_x5, wr_x6, wr_x7, wr_x8, wr_x9, wr_x10, wr_x11, wr_x12, wr_x13, wr_x14, wr_x15, wr_x16, wr_x17, wr_x18, wr_x19, wr_x20, wr_x21, wr_x22, wr_x23, wr_x24, wr_x25, wr_x26, wr_x27, wr_x28, wr_x30, BitVec.add_assoc, BitVec.reduceAdd, State.spAligned, mkS_sp, hcw,
      Memory.writeSized, hal']
    rw [← hsl]
    exact braidLoop (env_write1 hE _) c q ((bs.length - q) / 40 - 1) 0
      ((read64_write64_same _ _).trans (congrArg (BitVec.ofNat 64) (by omega))) (by omega) (by omega)
      (sub1 _ (by omega) (by omega)) (by simp) rfl (congrArg (BitVec.ofNat 64) (by omega))
      (by simp [braids]) (by simp [braids]) (by simp [braids]) (by simp [braids]) (by simp [braids])
      rfl rfl rfl rfl

end ZlibCrc32.Crcz.PartFS

namespace ZlibCrc32.Crcz
alias setup := PartFS.setup
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


theorem awc_add' (x y : BitVec 64) : (AddWithCarry64 x y false).1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [AddWithCarry64, BitVec.toNat_setWidth]; omega

end ZlibCrc32.Crcz.PartT
end

section
/-! # Part P: the alignment prefix at `0x48` -/

namespace ZlibCrc32.Crcz.PartP

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Arm64 Arm64.Obj ZlibCrc32.Crcz ZlibCrc32.Crcz.PartT

theorem cb_take {bs : List (BitVec 8)} (c : BitVec 32) (k : ℕ) (h : k < bs.length) :
    tstep (crcBytes c (bs.take k)) bs[k] = crcBytes c (bs.take (k + 1)) := by
  rw [List.take_succ_eq_append_getElem h, crcBytes, crcBytes, List.foldl_append]; rfl

theorem al_eq (B : BitVec 64) (k : ℕ) (hk : k < 8) :
    ((B + BitVec.ofNat 64 k) &&& 7#64 == 0#64) = decide ((B.toNat + k) % 8 = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj, BitVec.toNat_and,
    show (7#64 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_add, BitVec.toNat_ofNat]
  simp only [BitVec.toNat_zero]
  omega

theorem al_eq0 (B : BitVec 64) :
    (B &&& 7#64 == 0#64) = decide (B.toNat % 8 = 0) := by
  have := al_eq B 0 (by decide); simpa using this

theorem sub_eq (L k : ℕ) (hk : k ≤ L) (hL : L < 2 ^ 64) :
    BitVec.ofNat 64 L - BitVec.ofNat 64 k = BitVec.ofNat 64 (L - k) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, toNat_ofNat_lt _ hL, toNat_ofNat_lt _ (by omega), toNat_ofNat_lt _ (by omega)]
  omega

theorem z_ne (L k : ℕ) (hk : k < L) (hL : L < 2 ^ 64) :
    (AddWithCarry64 (BitVec.ofNat 64 L) (~~~ BitVec.ofNat 64 k) true).2.z = false := by
  rw [awc_z, toNat_ofNat_lt _ hL, toNat_ofNat_lt _ (by omega)]; simp; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem alignPrefix {pl : Placement} {s0 : State} {bs : List (BitVec 8)} {m : Memory} {ps : PState}
    {R : Regs} (hE : Env pl s0 bs m) (crc : BitVec 32) (h47 : 47 ≤ bs.length)
    (h1 : R.x1 = s0.readReg64 (.gpr 1#5)) (h2 : R.x2 = BitVec.ofNat 64 bs.length)
    (h9 : R.x9 = (~~~ crc).setWidth 64) (h13 : R.x13 = pl.ρ crcTabSym) :
    ∃ q K, q + 40 * (K + 1) ≤ bs.length ∧
      Reach pl s0 ((braidedResult crc bs q K).setWidth 64)
        (mkS s0 m (spIn s0) (pl.base + 84#64) ps R) := by
  have hP := hE.hP; have hCL := hE.hCL; have hrun := hE.hrun; have hn := hE.hlen
  generalize hB : s0.readReg64 (.gpr 1#5) = B at h1
  have hbuf : RoBytes m B bs := hB ▸ hE.hbuf
  have h9' : R.x9 = (crcBytes (~~~ crc) (bs.take 0)).setWidth 64 := by simpa [crcBytes] using h9
  obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18,
    y19, y20, y21, y22, y23, y24, y25, y26, y27, y28, y30⟩ := R
  simp only at h1 h2 h9' h13
  subst y1 h2 h9' h13
  clear h9
  refine ⟨(8 - B.toNat % 8) % 8, (bs.length - (8 - B.toNat % 8) % 8) / 40 - 1, by omega, ?_⟩
  have fin : ∀ q : ℕ, q = (8 - B.toNat % 8) % 8 → ∀ (ps' : PState) (R' : Regs),
      R'.x1 = B + BitVec.ofNat 64 q → R'.x2 = BitVec.ofNat 64 (bs.length - q) →
      R'.x9 = (crcBytes (~~~ crc) (bs.take q)).setWidth 64 → R'.x13 = pl.ρ crcTabSym →
        Reach pl s0 ((braidedResult crc bs ((8 - B.toNat % 8) % 8)
          ((bs.length - (8 - B.toNat % 8) % 8) / 40 - 1)).setWidth 64)
          (mkS s0 m (spIn s0) (pl.base + 424#64) ps' R') := by
    intro q hq ps' R' e1 e2 e9 e13
    subst hq
    exact setup (ps := ps') hE (crcBytes (~~~ crc) (bs.take _)) _ (by omega) (by rw [e1, hB]) e2 e9 e13
  refine reach_step (stepM hrun (f_048 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, al_eq0]
  refine reach_step (stepM hrun (f_04c hP hCL)) ?_
  by_cases hj : B.toNat % 8 = 0
  · simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, decide_eq_true hj]
    exact fin 0 (by omega) _ _ (by simp) (by simp) rfl rfl
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, decide_eq_false hj]
  refine reach_step (stepM hrun (f_050 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  -- byte 0
  obtain ⟨cr0, rb0⟩ := ro_read8 hbuf 0 (by omega)
  simp only [BitVec.add_zero, show BitVec.ofNat 64 0 = 0#64 from rfl] at cr0 rb0
  refine reach_step (stepM hrun (f_054 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, cr0, rb0]
  refine reach_step (stepM hrun (f_058 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_05c hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine ldrT0 hrun (f_060 hP hCL) hE.hT rfl (by simp only [rd_x11]; exact idx_and _) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_064 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_068 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, cb_take (bs := bs) (~~~ crc) 0 (by omega)]
  refine reach_step (stepM hrun (f_06c hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, z_ne bs.length 1 (by omega) hn]
  refine reach_step (stepM hrun (f_070 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_074 hP hCL)) ?_
  have hA1 := al_eq B 1 (by decide)
  by_cases ha1 : (B.toNat + 1) % 8 = 0
  · simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, hA1, decide_eq_true ha1]
    refine reach_step (stepM hrun (f_188 hP hCL)) ?_
    simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
    refine reach_step (stepM hrun (f_18c hP hCL)) ?_
    simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
    refine reach_step (stepM hrun (f_190 hP hCL)) ?_
    simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
    exact fin 1 (by omega) _ _ rfl (by rw [sub_eq _ _ (by omega) hn]) rfl rfl
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, hA1, decide_eq_false ha1]
  -- byte 1
  obtain ⟨cr1, rb1⟩ := ro_read8 hbuf 1 (by omega)
  refine reach_step (stepM hrun (f_078 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, cr1, rb1]
  refine reach_step (stepM hrun (f_07c hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_080 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine ldrT0 hrun (f_084 hP hCL) hE.hT rfl (by simp only [rd_x10]; exact idx_and _) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_088 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_08c hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, cb_take (bs := bs) (~~~ crc) 1 (by omega)]
  refine reach_step (stepM hrun (f_090 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_094 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, z_ne bs.length 2 (by omega) hn]
  refine reach_step (stepM hrun (f_098 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_09c hP hCL)) ?_
  have hA2 := al_eq B 2 (by decide)
  by_cases ha2 : (B.toNat + 2) % 8 = 0
  · simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, hA2, decide_eq_true ha2]
    refine reach_step (stepM hrun (f_194 hP hCL)) ?_
    simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
    refine reach_step (stepM hrun (f_198 hP hCL)) ?_
    simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
    exact fin 2 (by omega) _ _ rfl (by rw [sub_eq _ _ (by omega) hn]) rfl rfl
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, hA2, decide_eq_false ha2]
  -- byte 2
  obtain ⟨cr2, rb2⟩ := ro_read8 hbuf 2 (by omega)
  refine reach_step (stepM hrun (f_0a0 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, cr2, rb2]
  refine reach_step (stepM hrun (f_0a4 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_0a8 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine ldrT0 hrun (f_0ac hP hCL) hE.hT rfl (by simp only [rd_x10]; exact idx_and _) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_0b0 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_0b4 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, cb_take (bs := bs) (~~~ crc) 2 (by omega)]
  refine reach_step (stepM hrun (f_0b8 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_0bc hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, z_ne bs.length 3 (by omega) hn]
  refine reach_step (stepM hrun (f_0c0 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_0c4 hP hCL)) ?_
  have hA3 := al_eq B 3 (by decide)
  by_cases ha3 : (B.toNat + 3) % 8 = 0
  · simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, hA3, decide_eq_true ha3]
    refine reach_step (stepM hrun (f_194 hP hCL)) ?_
    simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
    refine reach_step (stepM hrun (f_198 hP hCL)) ?_
    simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
    exact fin 3 (by omega) _ _ rfl (by rw [sub_eq _ _ (by omega) hn]) rfl rfl
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, hA3, decide_eq_false ha3]
  -- byte 3
  obtain ⟨cr3, rb3⟩ := ro_read8 hbuf 3 (by omega)
  refine reach_step (stepM hrun (f_0c8 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, cr3, rb3]
  refine reach_step (stepM hrun (f_0cc hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_0d0 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine ldrT0 hrun (f_0d4 hP hCL) hE.hT rfl (by simp only [rd_x10]; exact idx_and _) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_0d8 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_0dc hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, cb_take (bs := bs) (~~~ crc) 3 (by omega)]
  refine reach_step (stepM hrun (f_0e0 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_0e4 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, z_ne bs.length 4 (by omega) hn]
  refine reach_step (stepM hrun (f_0e8 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_0ec hP hCL)) ?_
  have hA4 := al_eq B 4 (by decide)
  by_cases ha4 : (B.toNat + 4) % 8 = 0
  · simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, hA4, decide_eq_true ha4]
    refine reach_step (stepM hrun (f_194 hP hCL)) ?_
    simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
    refine reach_step (stepM hrun (f_198 hP hCL)) ?_
    simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
    exact fin 4 (by omega) _ _ rfl (by rw [sub_eq _ _ (by omega) hn]) rfl rfl
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, hA4, decide_eq_false ha4]
  -- byte 4
  obtain ⟨cr4, rb4⟩ := ro_read8 hbuf 4 (by omega)
  refine reach_step (stepM hrun (f_0f0 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, cr4, rb4]
  refine reach_step (stepM hrun (f_0f4 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_0f8 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine ldrT0 hrun (f_0fc hP hCL) hE.hT rfl (by simp only [rd_x10]; exact idx_and _) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_100 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_104 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, cb_take (bs := bs) (~~~ crc) 4 (by omega)]
  refine reach_step (stepM hrun (f_108 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_10c hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, z_ne bs.length 5 (by omega) hn]
  refine reach_step (stepM hrun (f_110 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_114 hP hCL)) ?_
  have hA5 := al_eq B 5 (by decide)
  by_cases ha5 : (B.toNat + 5) % 8 = 0
  · simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, hA5, decide_eq_true ha5]
    refine reach_step (stepM hrun (f_194 hP hCL)) ?_
    simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
    refine reach_step (stepM hrun (f_198 hP hCL)) ?_
    simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
    exact fin 5 (by omega) _ _ rfl (by rw [sub_eq _ _ (by omega) hn]) rfl rfl
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, hA5, decide_eq_false ha5]
  -- byte 5
  obtain ⟨cr5, rb5⟩ := ro_read8 hbuf 5 (by omega)
  refine reach_step (stepM hrun (f_118 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, cr5, rb5]
  refine reach_step (stepM hrun (f_11c hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_120 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine ldrT0 hrun (f_124 hP hCL) hE.hT rfl (by simp only [rd_x10]; exact idx_and _) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_128 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_12c hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, cb_take (bs := bs) (~~~ crc) 5 (by omega)]
  refine reach_step (stepM hrun (f_130 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_134 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, z_ne bs.length 6 (by omega) hn]
  refine reach_step (stepM hrun (f_138 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_13c hP hCL)) ?_
  have hA6 := al_eq B 6 (by decide)
  by_cases ha6 : (B.toNat + 6) % 8 = 0
  · simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, hA6, decide_eq_true ha6]
    refine reach_step (stepM hrun (f_194 hP hCL)) ?_
    simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
    refine reach_step (stepM hrun (f_198 hP hCL)) ?_
    simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
    exact fin 6 (by omega) _ _ rfl (by rw [sub_eq _ _ (by omega) hn]) rfl rfl
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, hA6, decide_eq_false ha6]
  -- byte 6
  obtain ⟨cr6, rb6⟩ := ro_read8 hbuf 6 (by omega)
  refine reach_step (stepM hrun (f_140 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, cr6, rb6]
  refine reach_step (stepM hrun (f_144 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_148 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine ldrT0 hrun (f_14c hP hCL) hE.hT rfl (by simp only [rd_x10]; exact idx_and _) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_150 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_154 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, cb_take (bs := bs) (~~~ crc) 6 (by omega)]
  refine reach_step (stepM hrun (f_158 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_15c hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, z_ne bs.length 7 (by omega) hn]
  refine reach_step (stepM hrun (f_160 hP hCL)) ?_
  simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
  refine reach_step (stepM hrun (f_164 hP hCL)) ?_
  have hA7 := al_eq B 7 (by decide)
  by_cases ha7 : (B.toNat + 7) % 8 = 0
  · simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false, hA7, decide_eq_true ha7]
    refine reach_step (stepM hrun (f_194 hP hCL)) ?_
    simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
    refine reach_step (stepM hrun (f_198 hP hCL)) ?_
    simp only [ex_ldr, execLdr, ex_logicalShift, execLogicalShift, ex_logicalImm, execLogicalImm, ex_addSubImm,
      execAddSubImm, ex_bCond, ex_cbz, ex_b, evalLogical, evalAddSub, shiftVal, shift32, shift64,
      checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, evalAddrMode, MemWidth.bytes,
      Memory.readSized, State.readReg, State.readReg32, State.writeReg, mkS_mem, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, rd_xzr, wr_xzr, rd_x1, rd_x2, rd_x9, rd_x10, rd_x11,
      rd_x12, wr_x1, wr_x2, wr_x9, wr_x10, wr_x11, wr_x12, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.add_zero, BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.not_true,
      Bool.false_eq_true, if_false, if_true, ite_false, ite_true, BitVec.truncate_eq_setWidth,
      BitVec.reduceZeroExtend, BitVec.zeroExtend_eq_setWidth, BitVec.reduceSetWidth, sw8, sw32, xor_sw, Nat.reduceMod,
      awc_fst, awc_add', tval, ConditionHolds, Bool.not_false, Bool.true_eq_false]
    exact fin 7 (by omega) _ _ rfl (by rw [sub_eq _ _ (by omega) hn]) rfl rfl
  exfalso; omega

end ZlibCrc32.Crcz.PartP

namespace ZlibCrc32.Crcz
alias alignPrefix := PartP.alignPrefix
end ZlibCrc32.Crcz
end

section
namespace ZlibCrc32.Crcz
alias crcBytes_holds := holds32_crcBytes
alias braided_holds := holds32_braidedResult
end ZlibCrc32.Crcz
end

section
/-! # `crc32_z` meets its contract: entry, prologue, dispatch, and the outcome -/

namespace ZlibCrc32.Crcz

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Arm64 Arm64.Obj

/-! ## Frame slots in simp-normal form, and the prologue's memory -/

theorem slot_0 (s0 : State) : slot s0 0 = s0.sp + 18446744073709551520#64 := by
  rw [slot_eq s0 0 (by decide)]

theorem slot_1 (s0 : State) : slot s0 1 = s0.sp + 18446744073709551528#64 := by
  rw [slot_eq s0 1 (by decide)]

theorem slot_2 (s0 : State) : slot s0 2 = s0.sp + 18446744073709551536#64 := by
  rw [slot_eq s0 2 (by decide)]

theorem slot_3 (s0 : State) : slot s0 3 = s0.sp + 18446744073709551544#64 := by
  rw [slot_eq s0 3 (by decide)]

theorem slot_4 (s0 : State) : slot s0 4 = s0.sp + 18446744073709551552#64 := by
  rw [slot_eq s0 4 (by decide)]

theorem slot_5 (s0 : State) : slot s0 5 = s0.sp + 18446744073709551560#64 := by
  rw [slot_eq s0 5 (by decide)]

theorem slot_6 (s0 : State) : slot s0 6 = s0.sp + 18446744073709551568#64 := by
  rw [slot_eq s0 6 (by decide)]

theorem slot_7 (s0 : State) : slot s0 7 = s0.sp + 18446744073709551576#64 := by
  rw [slot_eq s0 7 (by decide)]

theorem slot_8 (s0 : State) : slot s0 8 = s0.sp + 18446744073709551584#64 := by
  rw [slot_eq s0 8 (by decide)]

theorem slot_9 (s0 : State) : slot s0 9 = s0.sp + 18446744073709551592#64 := by
  rw [slot_eq s0 9 (by decide)]

theorem slot_10 (s0 : State) : slot s0 10 = s0.sp + 18446744073709551600#64 := by
  rw [slot_eq s0 10 (by decide)]

theorem slot_11 (s0 : State) : slot s0 11 = s0.sp + 18446744073709551608#64 := by
  rw [slot_eq s0 11 (by decide)]

/-- The memory after the prologue's stores. -/
def proMem (s0 : State) : Memory :=
  (((((((((((s0.mem).write64 (slot s0 0) (s0.readReg64 (.gpr 30#5))).write64 (slot s0 2) (s0.readReg64 (.gpr 28#5))).write64 (slot s0 3) (s0.readReg64 (.gpr 27#5))).write64 (slot s0 4) (s0.readReg64 (.gpr 26#5))).write64 (slot s0 5) (s0.readReg64 (.gpr 25#5))).write64 (slot s0 6) (s0.readReg64 (.gpr 24#5))).write64 (slot s0 7) (s0.readReg64 (.gpr 23#5))).write64 (slot s0 8) (s0.readReg64 (.gpr 22#5))).write64 (slot s0 9) (s0.readReg64 (.gpr 21#5))).write64 (slot s0 10) (s0.readReg64 (.gpr 20#5))).write64 (slot s0 11) (s0.readReg64 (.gpr 19#5))

theorem prologue_mem {s0 : State} (hF0 : FrameOk s0 s0.mem) :
    FrameOk s0 (proMem s0) ∧ Saved s0 (proMem s0) ∧
    FrameOk s0 ((s0.mem).write64 (slot s0 0) (s0.readReg64 (.gpr 30#5))) ∧
    FrameOk s0 ((((s0.mem).write64 (slot s0 0) (s0.readReg64 (.gpr 30#5))).write64 (slot s0 2) (s0.readReg64 (.gpr 28#5))).write64 (slot s0 3) (s0.readReg64 (.gpr 27#5))) ∧
    FrameOk s0 ((((((s0.mem).write64 (slot s0 0) (s0.readReg64 (.gpr 30#5))).write64 (slot s0 2) (s0.readReg64 (.gpr 28#5))).write64 (slot s0 3) (s0.readReg64 (.gpr 27#5))).write64 (slot s0 4) (s0.readReg64 (.gpr 26#5))).write64 (slot s0 5) (s0.readReg64 (.gpr 25#5))) ∧
    FrameOk s0 ((((((((s0.mem).write64 (slot s0 0) (s0.readReg64 (.gpr 30#5))).write64 (slot s0 2) (s0.readReg64 (.gpr 28#5))).write64 (slot s0 3) (s0.readReg64 (.gpr 27#5))).write64 (slot s0 4) (s0.readReg64 (.gpr 26#5))).write64 (slot s0 5) (s0.readReg64 (.gpr 25#5))).write64 (slot s0 6) (s0.readReg64 (.gpr 24#5))).write64 (slot s0 7) (s0.readReg64 (.gpr 23#5))) ∧
    FrameOk s0 ((((((((((s0.mem).write64 (slot s0 0) (s0.readReg64 (.gpr 30#5))).write64 (slot s0 2) (s0.readReg64 (.gpr 28#5))).write64 (slot s0 3) (s0.readReg64 (.gpr 27#5))).write64 (slot s0 4) (s0.readReg64 (.gpr 26#5))).write64 (slot s0 5) (s0.readReg64 (.gpr 25#5))).write64 (slot s0 6) (s0.readReg64 (.gpr 24#5))).write64 (slot s0 7) (s0.readReg64 (.gpr 23#5))).write64 (slot s0 8) (s0.readReg64 (.gpr 22#5))).write64 (slot s0 9) (s0.readReg64 (.gpr 21#5))) ∧

    (s0.mem).canWrite (slot s0 0) 8 = true ∧
    ((s0.mem).write64 (slot s0 0) (s0.readReg64 (.gpr 30#5))).canWrite (slot s0 2) 8 = true ∧
    ((s0.mem).write64 (slot s0 0) (s0.readReg64 (.gpr 30#5))).canWrite (slot s0 3) 8 = true ∧
    ((((s0.mem).write64 (slot s0 0) (s0.readReg64 (.gpr 30#5))).write64 (slot s0 2) (s0.readReg64 (.gpr 28#5))).write64 (slot s0 3) (s0.readReg64 (.gpr 27#5))).canWrite (slot s0 4) 8 = true ∧
    ((((s0.mem).write64 (slot s0 0) (s0.readReg64 (.gpr 30#5))).write64 (slot s0 2) (s0.readReg64 (.gpr 28#5))).write64 (slot s0 3) (s0.readReg64 (.gpr 27#5))).canWrite (slot s0 5) 8 = true ∧
    ((((((s0.mem).write64 (slot s0 0) (s0.readReg64 (.gpr 30#5))).write64 (slot s0 2) (s0.readReg64 (.gpr 28#5))).write64 (slot s0 3) (s0.readReg64 (.gpr 27#5))).write64 (slot s0 4) (s0.readReg64 (.gpr 26#5))).write64 (slot s0 5) (s0.readReg64 (.gpr 25#5))).canWrite (slot s0 6) 8 = true ∧
    ((((((s0.mem).write64 (slot s0 0) (s0.readReg64 (.gpr 30#5))).write64 (slot s0 2) (s0.readReg64 (.gpr 28#5))).write64 (slot s0 3) (s0.readReg64 (.gpr 27#5))).write64 (slot s0 4) (s0.readReg64 (.gpr 26#5))).write64 (slot s0 5) (s0.readReg64 (.gpr 25#5))).canWrite (slot s0 7) 8 = true ∧
    ((((((((s0.mem).write64 (slot s0 0) (s0.readReg64 (.gpr 30#5))).write64 (slot s0 2) (s0.readReg64 (.gpr 28#5))).write64 (slot s0 3) (s0.readReg64 (.gpr 27#5))).write64 (slot s0 4) (s0.readReg64 (.gpr 26#5))).write64 (slot s0 5) (s0.readReg64 (.gpr 25#5))).write64 (slot s0 6) (s0.readReg64 (.gpr 24#5))).write64 (slot s0 7) (s0.readReg64 (.gpr 23#5))).canWrite (slot s0 8) 8 = true ∧
    ((((((((s0.mem).write64 (slot s0 0) (s0.readReg64 (.gpr 30#5))).write64 (slot s0 2) (s0.readReg64 (.gpr 28#5))).write64 (slot s0 3) (s0.readReg64 (.gpr 27#5))).write64 (slot s0 4) (s0.readReg64 (.gpr 26#5))).write64 (slot s0 5) (s0.readReg64 (.gpr 25#5))).write64 (slot s0 6) (s0.readReg64 (.gpr 24#5))).write64 (slot s0 7) (s0.readReg64 (.gpr 23#5))).canWrite (slot s0 9) 8 = true ∧
    ((((((((((s0.mem).write64 (slot s0 0) (s0.readReg64 (.gpr 30#5))).write64 (slot s0 2) (s0.readReg64 (.gpr 28#5))).write64 (slot s0 3) (s0.readReg64 (.gpr 27#5))).write64 (slot s0 4) (s0.readReg64 (.gpr 26#5))).write64 (slot s0 5) (s0.readReg64 (.gpr 25#5))).write64 (slot s0 6) (s0.readReg64 (.gpr 24#5))).write64 (slot s0 7) (s0.readReg64 (.gpr 23#5))).write64 (slot s0 8) (s0.readReg64 (.gpr 22#5))).write64 (slot s0 9) (s0.readReg64 (.gpr 21#5))).canWrite (slot s0 10) 8 = true ∧
    ((((((((((s0.mem).write64 (slot s0 0) (s0.readReg64 (.gpr 30#5))).write64 (slot s0 2) (s0.readReg64 (.gpr 28#5))).write64 (slot s0 3) (s0.readReg64 (.gpr 27#5))).write64 (slot s0 4) (s0.readReg64 (.gpr 26#5))).write64 (slot s0 5) (s0.readReg64 (.gpr 25#5))).write64 (slot s0 6) (s0.readReg64 (.gpr 24#5))).write64 (slot s0 7) (s0.readReg64 (.gpr 23#5))).write64 (slot s0 8) (s0.readReg64 (.gpr 22#5))).write64 (slot s0 9) (s0.readReg64 (.gpr 21#5))).canWrite (slot s0 11) 8 = true := by
  have F0 := hF0
  have F1 := (frameOk_write64 F0 0 (by decide) (s0.readReg64 (.gpr 30#5))).2
  have F2 := (frameOk_write64 F1 2 (by decide) (s0.readReg64 (.gpr 28#5))).2
  have F3 := (frameOk_write64 F2 3 (by decide) (s0.readReg64 (.gpr 27#5))).2
  have F4 := (frameOk_write64 F3 4 (by decide) (s0.readReg64 (.gpr 26#5))).2
  have F5 := (frameOk_write64 F4 5 (by decide) (s0.readReg64 (.gpr 25#5))).2
  have F6 := (frameOk_write64 F5 6 (by decide) (s0.readReg64 (.gpr 24#5))).2
  have F7 := (frameOk_write64 F6 7 (by decide) (s0.readReg64 (.gpr 23#5))).2
  have F8 := (frameOk_write64 F7 8 (by decide) (s0.readReg64 (.gpr 22#5))).2
  have F9 := (frameOk_write64 F8 9 (by decide) (s0.readReg64 (.gpr 21#5))).2
  have F10 := (frameOk_write64 F9 10 (by decide) (s0.readReg64 (.gpr 20#5))).2
  have F11 := (frameOk_write64 F10 11 (by decide) (s0.readReg64 (.gpr 19#5))).2
  refine ⟨F11, ?_, F1, F3, F5, F7, F9, (frameOk_write64 F0 0 (by decide) 0#64).1, (frameOk_write64 F1 2 (by decide) 0#64).1, (frameOk_write64 F1 3 (by decide) 0#64).1, (frameOk_write64 F3 4 (by decide) 0#64).1, (frameOk_write64 F3 5 (by decide) 0#64).1, (frameOk_write64 F5 6 (by decide) 0#64).1, (frameOk_write64 F5 7 (by decide) 0#64).1, (frameOk_write64 F7 8 (by decide) 0#64).1, (frameOk_write64 F7 9 (by decide) 0#64).1, (frameOk_write64 F9 10 (by decide) 0#64).1, (frameOk_write64 F9 11 (by decide) 0#64).1⟩
  unfold proMem Saved
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [read64_write64_slot 0 11 (by decide) (by decide) (by decide), read64_write64_slot 0 10 (by decide) (by decide) (by decide), read64_write64_slot 0 9 (by decide) (by decide) (by decide), read64_write64_slot 0 8 (by decide) (by decide) (by decide), read64_write64_slot 0 7 (by decide) (by decide) (by decide), read64_write64_slot 0 6 (by decide) (by decide) (by decide), read64_write64_slot 0 5 (by decide) (by decide) (by decide), read64_write64_slot 0 4 (by decide) (by decide) (by decide), read64_write64_slot 0 3 (by decide) (by decide) (by decide), read64_write64_slot 0 2 (by decide) (by decide) (by decide), read64_write64_same]
  · rw [read64_write64_slot 2 11 (by decide) (by decide) (by decide), read64_write64_slot 2 10 (by decide) (by decide) (by decide), read64_write64_slot 2 9 (by decide) (by decide) (by decide), read64_write64_slot 2 8 (by decide) (by decide) (by decide), read64_write64_slot 2 7 (by decide) (by decide) (by decide), read64_write64_slot 2 6 (by decide) (by decide) (by decide), read64_write64_slot 2 5 (by decide) (by decide) (by decide), read64_write64_slot 2 4 (by decide) (by decide) (by decide), read64_write64_slot 2 3 (by decide) (by decide) (by decide), read64_write64_same]
  · rw [read64_write64_slot 3 11 (by decide) (by decide) (by decide), read64_write64_slot 3 10 (by decide) (by decide) (by decide), read64_write64_slot 3 9 (by decide) (by decide) (by decide), read64_write64_slot 3 8 (by decide) (by decide) (by decide), read64_write64_slot 3 7 (by decide) (by decide) (by decide), read64_write64_slot 3 6 (by decide) (by decide) (by decide), read64_write64_slot 3 5 (by decide) (by decide) (by decide), read64_write64_slot 3 4 (by decide) (by decide) (by decide), read64_write64_same]
  · rw [read64_write64_slot 4 11 (by decide) (by decide) (by decide), read64_write64_slot 4 10 (by decide) (by decide) (by decide), read64_write64_slot 4 9 (by decide) (by decide) (by decide), read64_write64_slot 4 8 (by decide) (by decide) (by decide), read64_write64_slot 4 7 (by decide) (by decide) (by decide), read64_write64_slot 4 6 (by decide) (by decide) (by decide), read64_write64_slot 4 5 (by decide) (by decide) (by decide), read64_write64_same]
  · rw [read64_write64_slot 5 11 (by decide) (by decide) (by decide), read64_write64_slot 5 10 (by decide) (by decide) (by decide), read64_write64_slot 5 9 (by decide) (by decide) (by decide), read64_write64_slot 5 8 (by decide) (by decide) (by decide), read64_write64_slot 5 7 (by decide) (by decide) (by decide), read64_write64_slot 5 6 (by decide) (by decide) (by decide), read64_write64_same]
  · rw [read64_write64_slot 6 11 (by decide) (by decide) (by decide), read64_write64_slot 6 10 (by decide) (by decide) (by decide), read64_write64_slot 6 9 (by decide) (by decide) (by decide), read64_write64_slot 6 8 (by decide) (by decide) (by decide), read64_write64_slot 6 7 (by decide) (by decide) (by decide), read64_write64_same]
  · rw [read64_write64_slot 7 11 (by decide) (by decide) (by decide), read64_write64_slot 7 10 (by decide) (by decide) (by decide), read64_write64_slot 7 9 (by decide) (by decide) (by decide), read64_write64_slot 7 8 (by decide) (by decide) (by decide), read64_write64_same]
  · rw [read64_write64_slot 8 11 (by decide) (by decide) (by decide), read64_write64_slot 8 10 (by decide) (by decide) (by decide), read64_write64_slot 8 9 (by decide) (by decide) (by decide), read64_write64_same]
  · rw [read64_write64_slot 9 11 (by decide) (by decide) (by decide), read64_write64_slot 9 10 (by decide) (by decide) (by decide), read64_write64_same]
  · rw [read64_write64_slot 10 11 (by decide) (by decide) (by decide), read64_write64_same]
  · rw [read64_write64_same]

section
variable {pl : Placement} {s0 : State} {bs : List (BitVec 8)} {m : Memory} {R : Regs}

set_option maxHeartbeats 1000000 in
/-- The length dispatch at `0x2c` after `cmp x2, #47`. -/
theorem dispatch (hE : Env pl s0 bs m) (crc : BitVec 32)
    (h1 : R.x1 = s0.readReg64 (.gpr 1#5)) (h2 : R.x2 = BitVec.ofNat 64 bs.length)
    (h9 : R.x9 = (~~~ crc).setWidth 64) (h13 : R.x13 = pl.ρ crcTabSym) :
    ∃ X, Holds32 X (crc32Poly crc bs) ∧
      Reach pl s0 X (mkS s0 m (spIn s0) (pl.base + 56#64)
        (AddWithCarry64 (BitVec.ofNat 64 bs.length) (~~~ 47#64) true).2 R) := by
  have hP := hE.hP; have hCL := hE.hCL; have hrun := hE.hrun
  have hn := hE.hlen
  by_cases h47 : 47 ≤ bs.length
  · obtain ⟨q, K, hqK, hR⟩ := alignPrefix (ps := (AddWithCarry64 (BitVec.ofNat 64 bs.length) (~~~ 47#64) true).2)
      hE crc h47 h1 h2 h9 h13
    refine ⟨_, braided_holds crc bs q K hqK, ?_⟩
    refine reach_step (stepM hrun (f_02c hP hCL)) ?_
    simp only [ex_bCond, mkS_pstate, cond_CS, toNat_ofNat_lt _ hn, mkS_setPC, mkS_pc,
      BitVec.add_assoc, BitVec.reduceAdd, show (47#64 : BitVec 64).toNat = 47 from rfl,
      decide_eq_true h47, if_true]
    exact hR
  · refine ⟨_, crcBytes_holds crc bs, ?_⟩
    refine reach_step (stepM hrun (f_02c hP hCL)) ?_
    simp only [ex_bCond, mkS_pstate, cond_CS, toNat_ofNat_lt _ hn, mkS_advancePC, mkS_pc,
      BitVec.add_assoc, BitVec.reduceAdd, show (47#64 : BitVec 64).toNat = 47 from rfl,
      decide_eq_false h47, Bool.false_eq_true, if_false]
    refine reach_step (stepM hrun (f_030 hP hCL)) ?_
    simp only [ex_addSubImm, execAddSubImm, State.readReg, rd_x2, evalAddSub, State.writeReg,
      wr_xzr, mkS_setPState, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd, h2, ite_true,
      ite_false, Bool.false_eq_true, BitVec.reduceZeroExtend]
    by_cases h8 : 8 ≤ bs.length
    · refine reach_step (stepM hrun (f_034 hP hCL)) ?_
      simp only [ex_bCond, mkS_pstate, cond_CS, toNat_ofNat_lt _ hn, mkS_setPC, mkS_pc,
        BitVec.add_assoc, BitVec.reduceAdd, show (8#64 : BitVec 64).toNat = 8 from rfl,
        decide_eq_true h8, if_true]
      have := loop8 (ps := (AddWithCarry64 (BitVec.ofNat 64 bs.length) (~~~ 8#64) true).2) hE
        (~~~ crc) 0 (by omega) (by rw [h1]; simp) (by rw [h2, Nat.sub_zero]) h9 h13
      simpa using this
    · refine reach_step (stepM hrun (f_034 hP hCL)) ?_
      simp only [ex_bCond, mkS_pstate, cond_CS, toNat_ofNat_lt _ hn, mkS_advancePC, mkS_pc,
        BitVec.add_assoc, BitVec.reduceAdd, show (8#64 : BitVec 64).toNat = 8 from rfl,
        decide_eq_false h8, Bool.false_eq_true, if_false]
      refine reach_step (stepM hrun (f_038 hP hCL)) ?_
      by_cases h0 : bs.length = 0
      · have hb : bs = [] := List.eq_nil_of_length_eq_zero h0
        have hx2 : R.x2 = 0#64 := by rw [h2, h0]
        simp only [ex_cbz, State.readReg, rd_x2, hx2, beq_self_eq_true, bne_self_eq_false,
          Bool.false_eq_true, if_true, if_false, mkS_advancePC, mkS_pc, BitVec.add_assoc,
          BitVec.reduceAdd]
        refine reach_step (stepM hrun (f_03c hP hCL)) ?_
        simp only [ex_b, mkS_setPC, mkS_pc, BitVec.add_assoc, BitVec.reduceAdd]
        have := epi (ps := (AddWithCarry64 (BitVec.ofNat 64 bs.length) (~~~ 8#64) true).2) hP hCL
          hrun hE.hal hE.hF hE.hS (~~~ crc) h9
        simpa [hb, crcBytes] using this
      · have hx2 : (R.x2 == 0#64) = false := by
          rw [h2, beq_eq_false_iff_ne]; intro h; apply h0
          have := congrArg BitVec.toNat h; rw [toNat_ofNat_lt _ hn] at this; simpa using this
        simp only [ex_cbz, State.readReg, rd_x2, hx2, bne_iff_ne, ne_eq, Bool.not_false,
          Bool.true_eq_false, not_false_eq_true, if_true, mkS_setPC, mkS_pc, BitVec.add_assoc,
          BitVec.reduceAdd]
        have := tail (ps := (AddWithCarry64 (BitVec.ofNat 64 bs.length) (~~~ 8#64) true).2) hE
          (~~~ crc) 0 bs.length (by omega) (by omega) (by omega) (by rw [h1]; simp) h2 h9 h13
        simpa using this

/-- The memory after the prologue, in simp-normal form. -/
theorem proMem_eq (s0 : State) : proMem s0 =
    (((((((((((s0.mem).write64 (s0.sp + 18446744073709551520#64) (s0.readReg64 (.gpr 30#5))).write64 (s0.sp + 18446744073709551536#64) (s0.readReg64 (.gpr 28#5))).write64 (s0.sp + 18446744073709551544#64) (s0.readReg64 (.gpr 27#5))).write64 (s0.sp + 18446744073709551552#64) (s0.readReg64 (.gpr 26#5))).write64 (s0.sp + 18446744073709551560#64) (s0.readReg64 (.gpr 25#5))).write64 (s0.sp + 18446744073709551568#64) (s0.readReg64 (.gpr 24#5))).write64 (s0.sp + 18446744073709551576#64) (s0.readReg64 (.gpr 23#5))).write64 (s0.sp + 18446744073709551584#64) (s0.readReg64 (.gpr 22#5))).write64 (s0.sp + 18446744073709551592#64) (s0.readReg64 (.gpr 21#5))).write64 (s0.sp + 18446744073709551600#64) (s0.readReg64 (.gpr 20#5))).write64 (s0.sp + 18446744073709551608#64) (s0.readReg64 (.gpr 19#5)) := by
  unfold proMem
  rw [slot_0, slot_2, slot_3, slot_4, slot_5, slot_6, slot_7, slot_8, slot_9, slot_10, slot_11]

theorem mvn_val (x : BitVec 64) :
    BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32
      (BitVec.zeroExtend 64 (BitVec.truncate 32 0#64) ||| ~~~BitVec.zeroExtend 64
        (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x)) <<< (0 % 32)))))) =
      (~~~ (x.setWidth 32)).setWidth 64 := by
  ext i hi
  simp only [BitVec.getElem_setWidth, BitVec.getElem_or, BitVec.getElem_not, BitVec.truncate_eq_setWidth,
    BitVec.zeroExtend_eq_setWidth, Nat.zero_mod, BitVec.shiftLeft_zero]
  by_cases h : i < 32 <;> simp [h, BitVec.getLsbD_setWidth, BitVec.getElem_setWidth]

/-- The registers after the prologue. -/
def proRegs (pl : Placement) (s0 : State) : Regs :=
  { Regs.of s0 with
    x9 := (~~~ ((s0.readReg64 (.gpr 0#5)).setWidth 32)).setWidth 64
    x13 := pl.ρ crcTabSym }

set_option maxHeartbeats 4000000 in
/-- From the entry state: the prologue, then the dispatch. -/
theorem entry {pl : Placement} {s0 : State} {bs : List (BitVec 8)} {Rf : SepProp}
    (hP : zlibCrc32Lib.Placeable pl) (hCL0 : (prog pl).CodeLoaded s0.mem)
    (hrun : s0.status = .Running) (hal : s0.spAligned = true) (hpc : s0.pc = pl.base + 12#64)
    (hpre : s0.mem ⊨ (crc32zSpec pl).pre (some bs) s0 ∗ Rf) :
    ∃ X, Holds32 X (crc32Poly ((s0.readReg64 (.gpr 0#5)).setWidth 32) bs) ∧ Reach pl s0 X s0 := by
  obtain ⟨hx1, hx2, hbuf, hT, hU, hF0⟩ := pre_facts hpre
  obtain ⟨hFM, hSM, G1, G3, G5, G7, G9, cw0, cw2, cw3, cw4, cw5, cw6, cw7, cw8, cw9, cw10, cw11⟩ :=
    prologue_mem hF0
  rw [proMem_eq] at hFM hSM
  simp only [slot_0, slot_2, slot_3, slot_4, slot_5, slot_6, slot_7, slot_8, slot_9] at G1 G3 G5 G7 G9
  have L1 := codeLoaded_of_frame hF0 G1 hCL0
  have L3 := codeLoaded_of_frame hF0 G3 hCL0
  have L5 := codeLoaded_of_frame hF0 G5 hCL0
  have L7 := codeLoaded_of_frame hF0 G7 hCL0
  have L9 := codeLoaded_of_frame hF0 G9 hCL0
  simp only [slot_0, slot_1, slot_2, slot_3, slot_4, slot_5, slot_6, slot_7, slot_8, slot_9, slot_10, slot_11] at cw0 cw2 cw3 cw4 cw5 cw6 cw7 cw8 cw9 cw10 cw11
  have hn : bs.length < 2 ^ 64 := hx2 ▸ (s0.readReg64 (.gpr 2#5)).isLt
  have hx2' : s0.readReg64 (.gpr 2#5) = BitVec.ofNat 64 bs.length := by
    apply BitVec.eq_of_toNat_eq; rw [toNat_ofNat_lt _ hn, hx2]
  have hE : Env pl s0 bs ((((((((((((s0.mem).write64 (s0.sp + 18446744073709551520#64) (s0.readReg64 (.gpr 30#5))).write64 (s0.sp + 18446744073709551536#64) (s0.readReg64 (.gpr 28#5))).write64 (s0.sp + 18446744073709551544#64) (s0.readReg64 (.gpr 27#5))).write64 (s0.sp + 18446744073709551552#64) (s0.readReg64 (.gpr 26#5))).write64 (s0.sp + 18446744073709551560#64) (s0.readReg64 (.gpr 25#5))).write64 (s0.sp + 18446744073709551568#64) (s0.readReg64 (.gpr 24#5))).write64 (s0.sp + 18446744073709551576#64) (s0.readReg64 (.gpr 23#5))).write64 (s0.sp + 18446744073709551584#64) (s0.readReg64 (.gpr 22#5))).write64 (s0.sp + 18446744073709551592#64) (s0.readReg64 (.gpr 21#5))).write64 (s0.sp + 18446744073709551600#64) (s0.readReg64 (.gpr 20#5))).write64 (s0.sp + 18446744073709551608#64) (s0.readReg64 (.gpr 19#5))) :=
    ⟨hP, codeLoaded_of_frame hF0 hFM hCL0, hrun, hal, hFM, hSM, roBytes_of_frame hFM hbuf,
      roBytes_of_frame hFM hT, roBytes_of_frame hFM hU, hn, hbuf.2, hT.2, hU.2⟩
  have L11 := hE.hCL
  have hal0 : (s0.sp &&& 15#64 == 0#64) = true := hal
  have hal1 : (s0.sp + 18446744073709551520#64 &&& 15#64 == 0#64) = true :=
    aligned_add s0.sp _ (by decide) hal0
  have hx1' : (s0.readReg64 (.gpr 1#5) == 0#64) = false := by simpa using hx1
  suffices h : ∃ X, Holds32 X (crc32Poly ((s0.readReg64 (.gpr 0#5)).setWidth 32) bs) ∧
      Reach pl s0 X (mkS s0 s0.mem s0.sp (pl.base + 12#64) s0.pstate (Regs.of s0)) by
    rwa [← hpc, mkS_self] at h
  obtain ⟨X, hX, hR⟩ := dispatch hE ((s0.readReg64 (.gpr 0#5)).setWidth 32)
    (R := proRegs pl s0) rfl hx2' rfl rfl
  refine ⟨X, hX, ?_⟩
  refine reach_step (stepM hrun (f_000 hP hCL0)) ?_
  simp only [ex_cbz, ex_addSubImm, execAddSubImm, ex_logicalShift, execLogicalShift, ex_str, execStr, ex_stp,
      execStp, evalLogical, evalAddSub, shiftVal, shift32, shift64, State.readReg, State.readReg32,
      State.writeReg, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned,
      evalAddrMode, Memory.writeSized, MemWidth.bytes, mkS_mem, mkS_sp, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, rd_sp, wr_sp, rd_xzr, wr_xzr,
      rd_x0, rd_x1, rd_x2, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27,
      rd_x28, rd_x30, wr_x9, Regs.of, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend,
      Bool.false_eq_true, Bool.not_true, Bool.not_false, if_true, if_false, ite_true, ite_false,
      Bool.and_self, Bool.and_true, Bool.true_and, hx1']
  refine reach_step (stepM hrun (f_004 hP hCL0)) ?_
  simp only [ex_cbz, ex_addSubImm, execAddSubImm, ex_logicalShift, execLogicalShift, ex_str, execStr, ex_stp,
      execStp, evalLogical, evalAddSub, shiftVal, shift32, shift64, State.readReg, State.readReg32,
      State.writeReg, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned,
      evalAddrMode, Memory.writeSized, MemWidth.bytes, mkS_mem, mkS_sp, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, rd_sp, wr_sp, rd_xzr, wr_xzr,
      rd_x0, rd_x1, rd_x2, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27,
      rd_x28, rd_x30, wr_x9, Regs.of, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend,
      Bool.false_eq_true, Bool.not_true, Bool.not_false, if_true, if_false, ite_true, ite_false,
      Bool.and_self, Bool.and_true, Bool.true_and, hal0, cw0]
  refine reach_step (stepM hrun (f_008 hP L1)) ?_
  simp only [ex_cbz, ex_addSubImm, execAddSubImm, ex_logicalShift, execLogicalShift, ex_str, execStr, ex_stp,
      execStp, evalLogical, evalAddSub, shiftVal, shift32, shift64, State.readReg, State.readReg32,
      State.writeReg, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned,
      evalAddrMode, Memory.writeSized, MemWidth.bytes, mkS_mem, mkS_sp, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, rd_sp, wr_sp, rd_xzr, wr_xzr,
      rd_x0, rd_x1, rd_x2, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27,
      rd_x28, rd_x30, wr_x9, Regs.of, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend,
      Bool.false_eq_true, Bool.not_true, Bool.not_false, if_true, if_false, ite_true, ite_false,
      Bool.and_self, Bool.and_true, Bool.true_and]
  refine reach_step (stepM hrun (f_00c hP L1)) ?_
  simp only [ex_cbz, ex_addSubImm, execAddSubImm, ex_logicalShift, execLogicalShift, ex_str, execStr, ex_stp,
      execStp, evalLogical, evalAddSub, shiftVal, shift32, shift64, State.readReg, State.readReg32,
      State.writeReg, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned,
      evalAddrMode, Memory.writeSized, MemWidth.bytes, mkS_mem, mkS_sp, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, rd_sp, wr_sp, rd_xzr, wr_xzr,
      rd_x0, rd_x1, rd_x2, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27,
      rd_x28, rd_x30, wr_x9, Regs.of, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend,
      Bool.false_eq_true, Bool.not_true, Bool.not_false, if_true, if_false, ite_true, ite_false,
      Bool.and_self, Bool.and_true, Bool.true_and]
  refine reach_steps (reloc28 hP L1 hrun _) ?_
  refine reach_step (stepM hrun (f_018 hP L1)) ?_
  simp only [ex_cbz, ex_addSubImm, execAddSubImm, ex_logicalShift, execLogicalShift, ex_str, execStr, ex_stp,
      execStp, evalLogical, evalAddSub, shiftVal, shift32, shift64, State.readReg, State.readReg32,
      State.writeReg, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned,
      evalAddrMode, Memory.writeSized, MemWidth.bytes, mkS_mem, mkS_sp, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, rd_sp, wr_sp, rd_xzr, wr_xzr,
      rd_x0, rd_x1, rd_x2, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27,
      rd_x28, rd_x30, wr_x9, Regs.of, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend,
      Bool.false_eq_true, Bool.not_true, Bool.not_false, if_true, if_false, ite_true, ite_false,
      Bool.and_self, Bool.and_true, Bool.true_and, hal1, cw2, cw3]
  refine reach_step (stepM hrun (f_01c hP L3)) ?_
  simp only [ex_cbz, ex_addSubImm, execAddSubImm, ex_logicalShift, execLogicalShift, ex_str, execStr, ex_stp,
      execStp, evalLogical, evalAddSub, shiftVal, shift32, shift64, State.readReg, State.readReg32,
      State.writeReg, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned,
      evalAddrMode, Memory.writeSized, MemWidth.bytes, mkS_mem, mkS_sp, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, rd_sp, wr_sp, rd_xzr, wr_xzr,
      rd_x0, rd_x1, rd_x2, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27,
      rd_x28, rd_x30, wr_x9, Regs.of, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend,
      Bool.false_eq_true, Bool.not_true, Bool.not_false, if_true, if_false, ite_true, ite_false,
      Bool.and_self, Bool.and_true, Bool.true_and, hal1, cw4, cw5]
  refine reach_step (stepM hrun (f_020 hP L5)) ?_
  simp only [ex_cbz, ex_addSubImm, execAddSubImm, ex_logicalShift, execLogicalShift, ex_str, execStr, ex_stp,
      execStp, evalLogical, evalAddSub, shiftVal, shift32, shift64, State.readReg, State.readReg32,
      State.writeReg, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned,
      evalAddrMode, Memory.writeSized, MemWidth.bytes, mkS_mem, mkS_sp, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, rd_sp, wr_sp, rd_xzr, wr_xzr,
      rd_x0, rd_x1, rd_x2, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27,
      rd_x28, rd_x30, wr_x9, Regs.of, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend,
      Bool.false_eq_true, Bool.not_true, Bool.not_false, if_true, if_false, ite_true, ite_false,
      Bool.and_self, Bool.and_true, Bool.true_and, hal1, cw6, cw7]
  refine reach_step (stepM hrun (f_024 hP L7)) ?_
  simp only [ex_cbz, ex_addSubImm, execAddSubImm, ex_logicalShift, execLogicalShift, ex_str, execStr, ex_stp,
      execStp, evalLogical, evalAddSub, shiftVal, shift32, shift64, State.readReg, State.readReg32,
      State.writeReg, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned,
      evalAddrMode, Memory.writeSized, MemWidth.bytes, mkS_mem, mkS_sp, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, rd_sp, wr_sp, rd_xzr, wr_xzr,
      rd_x0, rd_x1, rd_x2, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27,
      rd_x28, rd_x30, wr_x9, Regs.of, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend,
      Bool.false_eq_true, Bool.not_true, Bool.not_false, if_true, if_false, ite_true, ite_false,
      Bool.and_self, Bool.and_true, Bool.true_and, hal1, cw8, cw9]
  refine reach_step (stepM hrun (f_028 hP L9)) ?_
  simp only [ex_cbz, ex_addSubImm, execAddSubImm, ex_logicalShift, execLogicalShift, ex_str, execStr, ex_stp,
      execStp, evalLogical, evalAddSub, shiftVal, shift32, shift64, State.readReg, State.readReg32,
      State.writeReg, checkAddrSPAligned, AddrMode.baseReg, checkRegSPAligned, State.spAligned,
      evalAddrMode, Memory.writeSized, MemWidth.bytes, mkS_mem, mkS_sp, mkS_pc, mkS_pstate,
      mkS_advancePC, mkS_setPC, mkS_setPState, mkS_setMem, rd_sp, wr_sp, rd_xzr, wr_xzr,
      rd_x0, rd_x1, rd_x2, rd_x19, rd_x20, rd_x21, rd_x22, rd_x23, rd_x24, rd_x25, rd_x26, rd_x27,
      rd_x28, rd_x30, wr_x9, Regs.of, BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceZeroExtend,
      Bool.false_eq_true, Bool.not_true, Bool.not_false, if_true, if_false, ite_true, ite_false,
      Bool.and_self, Bool.and_true, Bool.true_and, hal1, cw10, cw11]
  rw [mvn_val]; rw [← hx2'] at hR
  exact hR

end

theorem fnAddr_crc (pl : Placement) : zlibCrc32Lib.fnAddr pl "crc32_z" = pl.base + 12#64 := rfl

set_option maxHeartbeats 1000000 in
/-- `crc32_z` meets `crc32zSpec`. -/
theorem subroutineOk_crc32_z : zlibCrc32Lib.subroutineOk "crc32_z" crc32zSpec := by
  refine ⟨by decide, ?_⟩
  intro pl hP g Rf s0 hpc hrun hpre hal hCL
  change (prog pl).CodeLoaded s0.mem at hCL
  rw [fnAddr_crc] at hpc
  cases g with
  | none =>
    have hx1 := pre_none_facts hpre
    refine ⟨mkS s0 s0.mem s0.sp (s0.readReg64 (.gpr 30#5)) s0.pstate
      { Regs.of s0 with x0 := 0#64, x1 := 0#64 }, ?_, ?_⟩
    · suffices h : Steps (prog pl) (mkS s0 s0.mem s0.sp (pl.base + 12#64) s0.pstate (Regs.of s0))
          (mkS s0 s0.mem s0.sp (s0.readReg64 (.gpr 30#5)) s0.pstate
            { Regs.of s0 with x0 := 0#64, x1 := 0#64 }) by
        rwa [← hpc, mkS_self] at h
      refine Steps.step (stepM hrun (f_000 hP hCL)) ?_
      simp only [ex_cbz, State.readReg, rd_x1, Regs.of, hx1, beq_self_eq_true, if_true,
        Bool.false_eq_true, if_false, mkS_setPC, mkS_pc, BitVec.add_assoc, BitVec.reduceAdd]
      refine Steps.step (stepM hrun (f_040 hP hCL)) ?_
      simp only [ex_logicalShift, execLogicalShift, evalLogical, shiftVal, shift64, State.readReg,
        rd_xzr, State.writeReg, wr_x0, mkS_advancePC, BitVec.add_assoc, BitVec.reduceAdd,
        BitVec.zero_or, Nat.zero_mod, BitVec.shiftLeft_zero, Bool.false_eq_true, if_false,
        ite_false]
      refine Steps.step (stepM hrun (f_044 hP hCL)) ?_
      simp only [ex_ret, rd_x30, mkS_setPC]
      exact Steps.refl _
    · refine Or.inl ⟨⟨rfl, rfl, hrun⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
      exact post_none hpre _ rfl rfl
  | some bs =>
    obtain ⟨X, hX, sf, hsteps, hpcf, hspf, hrunf, hcs, hx0, hF⟩ := entry hP hCL hrun hal hpc hpre
    refine ⟨sf, hsteps, Or.inl ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspf, hcs⟩, ?_⟩⟩
    exact post_some hpre hF sf rfl (hx0 ▸ hX)

end ZlibCrc32.Crcz
end

open ZlibCrc32 in
theorem solution : zlibCrc32Lib.subroutineOk "crc32_z" crc32zSpec := ZlibCrc32.Crcz.subroutineOk_crc32_z
