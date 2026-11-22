-- Prove2me | solution 1 for ZlibCrc32.crc32_z_adrp_pairs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T13:26:01.413252+00:00
-- url     : https://prove2.me/submissions/d9785b1d-35a4-43f1-b21b-28ca13e5fc0c

import Mathlib.Tactic.IntervalCases
import Definitions.Def_ZlibCrc32_CrczModel

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

end ZlibCrc32.Crcz
end

section
/-! # Part R: the relocated `ADRP`/`ADD` pairs (adapted from the byte-table pilot)

Symbolic decoding of the relocated words for any placement, unrelaxed (`ADRP` + `ADD`) and
linker-relaxed (`NOP` + `ADR`). -/

namespace ZlibCrc32.Crcz.AdrpProof

open Arm64 Arm64.Obj ZlibCrc32.Crcz

set_option maxRecDepth 100000

abbrev crcTabSym : String := "crc_table [zlib_crc32]"
abbrev braidTabSym : String := "crc_braid_table [zlib_crc32]"

theorem beq_false_of_mask {w K A M C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A &&& M) :
    (w &&& M == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, ← hK, BitVec.and_assoc, BitVec.and_comm M K, ← BitVec.and_assoc]

theorem beq_false_of_mask' {w K A C : BitVec 32} (hK : w &&& K = A) (h : C &&& K ≠ A) :
    (w == C) = false := by
  simp only [beq_eq_false_iff_ne]
  intro he; apply h; rw [← he, hK]

theorem decode_adr_class (w : BitVec 32) (hK : w &&& 0x1f000000#32 = 0x10000000#32) :
    decode w = some (.adr (w.getLsbD 31) (Reg.fromZRBits (w.extractLsb' 0 5))
      (if w.getLsbD 31 then ((w.extractLsb' 5 19 ++ w.extractLsb' 29 2).signExtend 64) <<< 12
       else (w.extractLsb' 5 19 ++ w.extractLsb' 29 2).signExtend 64)) := by
  rw [decode]
  simp only [beq_false_of_mask' hK (C := 0xd503201f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4000001#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4200000#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd503201f#32) (M := 0xfffff01f#32) (by decide),
    beq_false_of_mask hK (C := 0#32) (M := 0xffff0000#32) (by decide),
    beq_false_of_mask hK (C := 0xd50b7420#32) (M := 0xffffffe0#32) (by decide), hK]
  simp

theorem decode_addimm_class (w : BitVec 32) (hK : w &&& 0x1f800000#32 = 0x11000000#32) :
    decode w = some (
      let op := AddSubOp.ofBits (w.getLsbD 30) (w.getLsbD 29)
      .addSubImm (RegWidth.ofBool (w.getLsbD 31)) op
        (if op.setsFlags then Reg.fromZRBits (w.extractLsb' 0 5) else Reg.fromSPBits (w.extractLsb' 0 5))
        (Reg.fromSPBits (w.extractLsb' 5 5)) (w.extractLsb' 10 12) (w.getLsbD 22)) := by
  rw [decode]
  simp only [beq_false_of_mask' hK (C := 0xd503201f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4000001#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd4200000#32) (M := 0xffe0001f#32) (by decide),
    beq_false_of_mask hK (C := 0xd503201f#32) (M := 0xfffff01f#32) (by decide),
    beq_false_of_mask hK (C := 0#32) (M := 0xffff0000#32) (by decide),
    beq_false_of_mask hK (C := 0xd50b7420#32) (M := 0xffffffe0#32) (by decide),
    beq_false_of_mask hK (C := 0x10000000#32) (M := 0x1f000000#32) (by decide), hK]
  simp

theorem hi_bits32 (D : BitVec 64) (h1 : -(2^32:Int) ≤ D.toInt) (h2 : D.toInt < 2^32) :
    ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32 := by
  intro i hi1 hi2
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  have hlt := D.isLt
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  interval_cases i <;> (try simp only [decide_eq_decide]) <;> (try split at h1) <;> omega

theorem hi_bits20 (D : BitVec 64) (h1 : -(2^20:Int) ≤ D.toInt) (h2 : D.toInt < 2^20) :
    ∀ i, 20 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 20 := by
  intro i hi1 hi2
  rw [BitVec.toInt_eq_toNat_cond] at h1 h2
  have hlt := D.isLt
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  interval_cases i <;> (try simp only [decide_eq_decide]) <;> (try split at h1) <;> omega

theorem pageOf_eq (x : BitVec 64) : pageOf x = (x >>> 12) <<< 12 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [pageOf, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

theorem pageOf_toNat (x : BitVec 64) : (pageOf x).toNat = x.toNat / 4096 * 4096 := by
  rw [pageOf_eq]; simp [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]; omega

theorem lo_bits (a b : BitVec 64) : ∀ i, i < 12 → (pageOf a - pageOf b).getLsbD i = false := by
  intro i hi
  have h : (pageOf a - pageOf b).toNat % 4096 = 0 := by
    rw [BitVec.toNat_sub, pageOf_toNat, pageOf_toNat]
    have := a.isLt; have := b.isLt; omega
  simp only [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  generalize (pageOf a - pageOf b).toNat = n at h ⊢
  interval_cases i <;> simp <;> omega



theorem decode_nop : decode nopWord = some .nop := by decide


section words13
variable (D : BitVec 64)

theorem wA_mask13 : adrpWordOff 0x9000000d#32 D &&& 0x1f000000#32 = 0x10000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wA_3113 : (adrpWordOff 0x9000000d#32 D).getLsbD 31 = true := by
  simp [adrpWordOff]

theorem wA_rd13 : (adrpWordOff 0x9000000d#32 D).extractLsb' 0 5 = 13#5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wA_off13 (hlo : ∀ i, i < 12 → D.getLsbD i = false)
    (hhi : ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32) :
    ((adrpWordOff 0x9000000d#32 D).extractLsb' 5 19 ++
      (adrpWordOff 0x9000000d#32 D).extractLsb' 29 2).signExtend 64 <<< 12 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getMsbD]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | exact hlo _ (by omega) | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm


theorem wC_mask13 : adrWordOff 0x1000000d#32 D &&& 0x1f000000#32 = 0x10000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wC_3113 : (adrWordOff 0x1000000d#32 D).getLsbD 31 = false := by
  simp [adrWordOff]

theorem wC_rd13 : (adrWordOff 0x1000000d#32 D).extractLsb' 0 5 = 13#5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wC_off13 (hhi : ∀ i, 20 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 20) :
    ((adrWordOff 0x1000000d#32 D).extractLsb' 5 19 ++
      (adrWordOff 0x1000000d#32 D).extractLsb' 29 2).signExtend 64 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | rfl | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm

theorem wB_mask13 : lo12Word 0 0x910001ad#32 D &&& 0x1f800000#32 = 0x11000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wB_bits13 : (lo12Word 0 0x910001ad#32 D).getLsbD 31 = true ∧
    (lo12Word 0 0x910001ad#32 D).getLsbD 30 = false ∧
    (lo12Word 0 0x910001ad#32 D).getLsbD 29 = false ∧
    (lo12Word 0 0x910001ad#32 D).getLsbD 22 = false := by
  simp [lo12Word]

theorem wB_rd13 : (lo12Word 0 0x910001ad#32 D).extractLsb' 0 5 = 13#5 ∧
    (lo12Word 0 0x910001ad#32 D).extractLsb' 5 5 = 13#5 := by
  constructor <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem wB_imm13 : (lo12Word 0 0x910001ad#32 D).extractLsb' 10 12 = D.extractLsb' 0 12 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

end words13

theorem decode_A13 {P T : BitVec 64} (hr : AdrpInRange P T) :
    decode (adrpWord 0x9000000d#32 P T) = some (.adr true (.gpr 13#5) (pageOf T - pageOf P)) := by
  rw [adrpWord, decode_adr_class _ (wA_mask13 _), wA_3113, wA_rd13,
    wA_off13 _ (lo_bits T P) (hi_bits32 _ hr.1 hr.2)]
  rfl

theorem decode_C13 {P T : BitVec 64} (hr : AdrInRange P T) :
    decode (adrWord (adrTemplate 0x910001ad#32) P T) = some (.adr false (.gpr 13#5) (T - P)) := by
  rw [adrWord, show adrTemplate 0x910001ad#32 = 0x1000000d#32 by decide,
    decode_adr_class _ (wC_mask13 _), wC_3113, wC_rd13, if_neg (by decide), wC_off13 _ (hi_bits20 _ hr.1 hr.2)]
  rfl

theorem decode_B13 (T : BitVec 64) :
    decode (lo12Word 0 0x910001ad#32 T) =
      some (.addSubImm .W64 .ADD (.gpr 13#5) (.gpr 13#5) (T.extractLsb' 0 12) false) := by
  obtain ⟨b31, b30, b29, b22⟩ := wB_bits13 T
  rw [decode_addimm_class _ (wB_mask13 _), b31, b30, b29, b22, wB_rd13 T |>.1, wB_rd13 T |>.2, wB_imm13]
  rfl



section words12
variable (D : BitVec 64)

theorem wA_mask12 : adrpWordOff 0x9000000c#32 D &&& 0x1f000000#32 = 0x10000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wA_3112 : (adrpWordOff 0x9000000c#32 D).getLsbD 31 = true := by
  simp [adrpWordOff]

theorem wA_rd12 : (adrpWordOff 0x9000000c#32 D).extractLsb' 0 5 = 12#5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wA_off12 (hlo : ∀ i, i < 12 → D.getLsbD i = false)
    (hhi : ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32) :
    ((adrpWordOff 0x9000000c#32 D).extractLsb' 5 19 ++
      (adrpWordOff 0x9000000c#32 D).extractLsb' 29 2).signExtend 64 <<< 12 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getMsbD]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | exact hlo _ (by omega) | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm


theorem wC_mask12 : adrWordOff 0x1000000c#32 D &&& 0x1f000000#32 = 0x10000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wC_3112 : (adrWordOff 0x1000000c#32 D).getLsbD 31 = false := by
  simp [adrWordOff]

theorem wC_rd12 : (adrWordOff 0x1000000c#32 D).extractLsb' 0 5 = 12#5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wC_off12 (hhi : ∀ i, 20 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 20) :
    ((adrWordOff 0x1000000c#32 D).extractLsb' 5 19 ++
      (adrWordOff 0x1000000c#32 D).extractLsb' 29 2).signExtend 64 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | rfl | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm

theorem wB_mask12 : lo12Word 0 0x9100018c#32 D &&& 0x1f800000#32 = 0x11000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wB_bits12 : (lo12Word 0 0x9100018c#32 D).getLsbD 31 = true ∧
    (lo12Word 0 0x9100018c#32 D).getLsbD 30 = false ∧
    (lo12Word 0 0x9100018c#32 D).getLsbD 29 = false ∧
    (lo12Word 0 0x9100018c#32 D).getLsbD 22 = false := by
  simp [lo12Word]

theorem wB_rd12 : (lo12Word 0 0x9100018c#32 D).extractLsb' 0 5 = 12#5 ∧
    (lo12Word 0 0x9100018c#32 D).extractLsb' 5 5 = 12#5 := by
  constructor <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem wB_imm12 : (lo12Word 0 0x9100018c#32 D).extractLsb' 10 12 = D.extractLsb' 0 12 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

end words12

theorem decode_A12 {P T : BitVec 64} (hr : AdrpInRange P T) :
    decode (adrpWord 0x9000000c#32 P T) = some (.adr true (.gpr 12#5) (pageOf T - pageOf P)) := by
  rw [adrpWord, decode_adr_class _ (wA_mask12 _), wA_3112, wA_rd12,
    wA_off12 _ (lo_bits T P) (hi_bits32 _ hr.1 hr.2)]
  rfl

theorem decode_C12 {P T : BitVec 64} (hr : AdrInRange P T) :
    decode (adrWord (adrTemplate 0x9100018c#32) P T) = some (.adr false (.gpr 12#5) (T - P)) := by
  rw [adrWord, show adrTemplate 0x9100018c#32 = 0x1000000c#32 by decide,
    decode_adr_class _ (wC_mask12 _), wC_3112, wC_rd12, if_neg (by decide), wC_off12 _ (hi_bits20 _ hr.1 hr.2)]
  rfl

theorem decode_B12 (T : BitVec 64) :
    decode (lo12Word 0 0x9100018c#32 T) =
      some (.addSubImm .W64 .ADD (.gpr 12#5) (.gpr 12#5) (T.extractLsb' 0 12) false) := by
  obtain ⟨b31, b30, b29, b22⟩ := wB_bits12 T
  rw [decode_addimm_class _ (wB_mask12 _), b31, b30, b29, b22, wB_rd12 T |>.1, wB_rd12 T |>.2, wB_imm12]
  rfl



theorem target_sym (pl : Placement) (o : Nat) (k : RelocKind) (sym : String)
    (hlk : lookup sym zlibCrc32Text.symbols = none) :
    zlibCrc32Text.target pl { off := o, kind := k, sym := sym } = pl.ρ sym := by
  simp [CodeBlock.target, CodeBlock.resolve, hlk, addSignedAddr]

theorem pw_adrp13 (pl : Placement) (o : Nat) (ho : o = 28 ∨ o = 1040) :
    zlibCrc32Text.patchedWord pl o =
      if pl.relax o then nopWord else adrpWord 0x9000000d#32 (pl.base + BitVec.ofNat 64 o) (pl.ρ crcTabSym) := by
  have hr : zlibCrc32Text.relocAt? o = some { off := o, kind := .adrpHi21, sym := crcTabSym } := by
    rcases ho with rfl | rfl <;> rfl
  have h1 : zlibCrc32Text.relaxableAt o = true := by rcases ho with rfl | rfl <;> decide
  have h2 : zlibCrc32Text.relaxableAt (o - 4) = false := by rcases ho with rfl | rfl <;> decide
  have hw : zlibCrc32Text.wordAt o = 0x9000000d#32 := by rcases ho with rfl | rfl <;> decide +kernel
  have hlk : lookup crcTabSym zlibCrc32Text.symbols = none := by decide
  have h4 : (4 ≤ o) = True := by rcases ho with rfl | rfl <;> simp
  cases h : pl.relax o <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h1, h2, hr, hw, h4,
      CodeBlock.relocTarget, CodeBlock.b2bNext?, CodeBlock.undefWeakBranch, CodeBlock.target,
      CodeBlock.resolve, hlk, addSignedAddr, patchRelocWord, RelocKind.isGotOrTlsIe]

theorem pw_add13 (pl : Placement) (o : Nat) (ho : o = 28 ∨ o = 1040) :
    zlibCrc32Text.patchedWord pl (o + 4) =
      if pl.relax o then adrWord (adrTemplate 0x910001ad#32) (pl.base + BitVec.ofNat 64 (o + 4)) (pl.ρ crcTabSym)
      else lo12Word 0 0x910001ad#32 (pl.ρ crcTabSym) := by
  have hr : zlibCrc32Text.relocAt? (o + 4) = some { off := o + 4, kind := .addLo12, sym := crcTabSym } := by
    rcases ho with rfl | rfl <;> rfl
  have h1 : zlibCrc32Text.relaxableAt o = true := by rcases ho with rfl | rfl <;> decide
  have h2 : zlibCrc32Text.relaxableAt (o + 4) = false := by rcases ho with rfl | rfl <;> decide
  have hw : zlibCrc32Text.wordAt (o + 4) = 0x910001ad#32 := by rcases ho with rfl | rfl <;> decide +kernel
  have hlk : lookup crcTabSym zlibCrc32Text.symbols = none := by decide
  have h4 : (4 ≤ o + 4) = True := by simp
  cases h : pl.relax o <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h1, h2, hr, hw, h4,
      CodeBlock.relocTarget, CodeBlock.b2bNext?, CodeBlock.undefWeakBranch, CodeBlock.target,
      CodeBlock.resolve, hlk, addSignedAddr, patchRelocWord, RelocKind.isGotOrTlsIe]

theorem range_adrp13 {pl : Placement} (hP : zlibCrc32Lib.Placeable pl) (o : Nat) (ho : o = 28 ∨ o = 1040) :
    AdrpInRange (pl.base + BitVec.ofNat 64 o) (pl.ρ crcTabSym) := by
  have hmem : ({ off := o, kind := .adrpHi21, sym := crcTabSym } : RelocEntry) ∈ zlibCrc32Text.relocs := by
    rcases ho with rfl | rfl <;> decide
  have h := (hP.text.relocs_ok _ hmem).2.2
  have ht : zlibCrc32Text.relocTarget pl o { off := o, kind := .adrpHi21, sym := crcTabSym } = pl.ρ crcTabSym := by
    simp only [CodeBlock.relocTarget, CodeBlock.b2bNext?]
    simp [target_sym pl o _ crcTabSym (by decide)]
  simp only [zlibCrc32Lib] at h
  rw [ht] at h
  exact h

theorem range_adr13 {pl : Placement} (hP : zlibCrc32Lib.Placeable pl) (o : Nat) (ho : o = 28 ∨ o = 1040)
    (hrel : pl.relax o = true) :
    AdrInRange (pl.base + BitVec.ofNat 64 (o + 4)) (pl.ρ crcTabSym) := by
  have h1 : zlibCrc32Text.relaxableAt o = true := by rcases ho with rfl | rfl <;> decide
  have hr : zlibCrc32Text.relocAt? (o + 4) = some { off := o + 4, kind := .addLo12, sym := crcTabSym } := by
    rcases ho with rfl | rfl <;> rfl
  have hPt : zlibCrc32Text.Placeable pl := hP.text
  have h := hPt.relaxed_ok o _ (by simp [CodeBlock.relaxedAt, h1, hrel]) hr
  rwa [target_sym pl _ _ crcTabSym (by decide)] at h


theorem pw_adrp12 (pl : Placement) (o : Nat) (ho : o = 456) :
    zlibCrc32Text.patchedWord pl o =
      if pl.relax o then nopWord else adrpWord 0x9000000c#32 (pl.base + BitVec.ofNat 64 o) (pl.ρ braidTabSym) := by
  have hr : zlibCrc32Text.relocAt? o = some { off := o, kind := .adrpHi21, sym := braidTabSym } := by
    subst ho <;> rfl
  have h1 : zlibCrc32Text.relaxableAt o = true := by subst ho <;> decide
  have h2 : zlibCrc32Text.relaxableAt (o - 4) = false := by subst ho <;> decide
  have hw : zlibCrc32Text.wordAt o = 0x9000000c#32 := by subst ho <;> decide +kernel
  have hlk : lookup braidTabSym zlibCrc32Text.symbols = none := by decide
  have h4 : (4 ≤ o) = True := by subst ho <;> simp
  cases h : pl.relax o <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h1, h2, hr, hw, h4,
      CodeBlock.relocTarget, CodeBlock.b2bNext?, CodeBlock.undefWeakBranch, CodeBlock.target,
      CodeBlock.resolve, hlk, addSignedAddr, patchRelocWord, RelocKind.isGotOrTlsIe]

theorem pw_add12 (pl : Placement) (o : Nat) (ho : o = 456) :
    zlibCrc32Text.patchedWord pl (o + 4) =
      if pl.relax o then adrWord (adrTemplate 0x9100018c#32) (pl.base + BitVec.ofNat 64 (o + 4)) (pl.ρ braidTabSym)
      else lo12Word 0 0x9100018c#32 (pl.ρ braidTabSym) := by
  have hr : zlibCrc32Text.relocAt? (o + 4) = some { off := o + 4, kind := .addLo12, sym := braidTabSym } := by
    subst ho <;> rfl
  have h1 : zlibCrc32Text.relaxableAt o = true := by subst ho <;> decide
  have h2 : zlibCrc32Text.relaxableAt (o + 4) = false := by subst ho <;> decide
  have hw : zlibCrc32Text.wordAt (o + 4) = 0x9100018c#32 := by subst ho <;> decide +kernel
  have hlk : lookup braidTabSym zlibCrc32Text.symbols = none := by decide
  have h4 : (4 ≤ o + 4) = True := by simp
  cases h : pl.relax o <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h1, h2, hr, hw, h4,
      CodeBlock.relocTarget, CodeBlock.b2bNext?, CodeBlock.undefWeakBranch, CodeBlock.target,
      CodeBlock.resolve, hlk, addSignedAddr, patchRelocWord, RelocKind.isGotOrTlsIe]

theorem range_adrp12 {pl : Placement} (hP : zlibCrc32Lib.Placeable pl) (o : Nat) (ho : o = 456) :
    AdrpInRange (pl.base + BitVec.ofNat 64 o) (pl.ρ braidTabSym) := by
  have hmem : ({ off := o, kind := .adrpHi21, sym := braidTabSym } : RelocEntry) ∈ zlibCrc32Text.relocs := by
    subst ho <;> decide
  have h := (hP.text.relocs_ok _ hmem).2.2
  have ht : zlibCrc32Text.relocTarget pl o { off := o, kind := .adrpHi21, sym := braidTabSym } = pl.ρ braidTabSym := by
    simp only [CodeBlock.relocTarget, CodeBlock.b2bNext?]
    simp [target_sym pl o _ braidTabSym (by decide)]
  simp only [zlibCrc32Lib] at h
  rw [ht] at h
  exact h

theorem range_adr12 {pl : Placement} (hP : zlibCrc32Lib.Placeable pl) (o : Nat) (ho : o = 456)
    (hrel : pl.relax o = true) :
    AdrInRange (pl.base + BitVec.ofNat 64 (o + 4)) (pl.ρ braidTabSym) := by
  have h1 : zlibCrc32Text.relaxableAt o = true := by subst ho <;> decide
  have hr : zlibCrc32Text.relocAt? (o + 4) = some { off := o + 4, kind := .addLo12, sym := braidTabSym } := by
    subst ho <;> rfl
  have hPt : zlibCrc32Text.Placeable pl := hP.text
  have h := hPt.relaxed_ok o _ (by simp [CodeBlock.relaxedAt, h1, hrel]) hr
  rwa [target_sym pl _ _ braidTabSym (by decide)] at h

theorem adrp_pairs (pl : Placement) (hP : zlibCrc32Lib.Placeable pl) (m : Memory)
    (hCL : (zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)).CodeLoaded m)
    (o : Nat) (rd : BitVec 5) (sym : String)
    (h : (o = 28 ∧ rd = 13#5 ∧ sym = "crc_table [zlib_crc32]") ∨
      (o = 456 ∧ rd = 12#5 ∧ sym = "crc_braid_table [zlib_crc32]") ∨
      (o = 1040 ∧ rd = 13#5 ∧ sym = "crc_table [zlib_crc32]")) :
    ((zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)).fetchMem m
          (pl.base + BitVec.ofNat 64 o) =
        some (.adr true (.gpr rd) (pageOf (pl.ρ sym) - pageOf (pl.base + BitVec.ofNat 64 o))) ∧
      (zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)).fetchMem m
          (pl.base + BitVec.ofNat 64 (o + 4)) =
        some (.addSubImm .W64 .ADD (.gpr rd) (.gpr rd) ((pl.ρ sym).extractLsb' 0 12) false)) ∨
    ((zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)).fetchMem m
          (pl.base + BitVec.ofNat 64 o) = some .nop ∧
      (zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)).fetchMem m
          (pl.base + BitVec.ofNat 64 (o + 4)) =
        some (.adr false (.gpr rd) (pl.ρ sym - (pl.base + BitVec.ofNat 64 (o + 4))))) := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · have hf2 := fetch_word hP hCL (off := 28 + 4) (by decide) (by decide)
    rw [pw_add13 pl 28 (Or.inl rfl)] at hf2
    have hf1 := fetch_word hP hCL (off := 28) (by decide) (by decide)
    rw [pw_adrp13 pl 28 (Or.inl rfl)] at hf1
    cases hr : pl.relax 28
    · simp only [hr, Bool.false_eq_true, if_false] at hf1 hf2
      rw [decode_A13 (range_adrp13 hP 28 (Or.inl rfl))] at hf1
      rw [decode_B13] at hf2
      exact Or.inl ⟨hf1, hf2⟩
    · simp only [hr, if_true] at hf1 hf2
      rw [decode_nop] at hf1
      rw [decode_C13 (range_adr13 hP 28 (Or.inl rfl) hr)] at hf2
      exact Or.inr ⟨hf1, hf2⟩
  · have hf2 := fetch_word hP hCL (off := 456 + 4) (by decide) (by decide)
    rw [pw_add12 pl 456 rfl] at hf2
    have hf1 := fetch_word hP hCL (off := 456) (by decide) (by decide)
    rw [pw_adrp12 pl 456 rfl] at hf1
    cases hr : pl.relax 456
    · simp only [hr, Bool.false_eq_true, if_false] at hf1 hf2
      rw [decode_A12 (range_adrp12 hP 456 rfl)] at hf1
      rw [decode_B12] at hf2
      exact Or.inl ⟨hf1, hf2⟩
    · simp only [hr, if_true] at hf1 hf2
      rw [decode_nop] at hf1
      rw [decode_C12 (range_adr12 hP 456 rfl hr)] at hf2
      exact Or.inr ⟨hf1, hf2⟩
  · have hf2 := fetch_word hP hCL (off := 1040 + 4) (by decide) (by decide)
    rw [pw_add13 pl 1040 (Or.inr rfl)] at hf2
    have hf1 := fetch_word hP hCL (off := 1040) (by decide) (by decide)
    rw [pw_adrp13 pl 1040 (Or.inr rfl)] at hf1
    cases hr : pl.relax 1040
    · simp only [hr, Bool.false_eq_true, if_false] at hf1 hf2
      rw [decode_A13 (range_adrp13 hP 1040 (Or.inr rfl))] at hf1
      rw [decode_B13] at hf2
      exact Or.inl ⟨hf1, hf2⟩
    · simp only [hr, if_true] at hf1 hf2
      rw [decode_nop] at hf1
      rw [decode_C13 (range_adr13 hP 1040 (Or.inr rfl) hr)] at hf2
      exact Or.inr ⟨hf1, hf2⟩

end ZlibCrc32.Crcz.AdrpProof
end

open Arm64 Arm64.Obj
open ZlibCrc32 ZlibCrc32 in
theorem solution (pl : Placement) (hP : zlibCrc32Lib.Placeable pl) (m : Memory)
    (hCL : (zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)).CodeLoaded m)
    (o : Nat) (rd : BitVec 5) (sym : String)
    (h : (o = 28 ∧ rd = 13#5 ∧ sym = "crc_table [zlib_crc32]") ∨
      (o = 456 ∧ rd = 12#5 ∧ sym = "crc_braid_table [zlib_crc32]") ∨
      (o = 1040 ∧ rd = 13#5 ∧ sym = "crc_table [zlib_crc32]")) :
    ((zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)).fetchMem m
          (pl.base + BitVec.ofNat 64 o) =
        some (.adr true (.gpr rd) (pageOf (pl.ρ sym) - pageOf (pl.base + BitVec.ofNat 64 o))) ∧
      (zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)).fetchMem m
          (pl.base + BitVec.ofNat 64 (o + 4)) =
        some (.addSubImm .W64 .ADD (.gpr rd) (.gpr rd) ((pl.ρ sym).extractLsb' 0 12) false)) ∨
    ((zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)).fetchMem m
          (pl.base + BitVec.ofNat 64 o) = some .nop ∧
      (zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)).fetchMem m
          (pl.base + BitVec.ofNat 64 (o + 4)) =
        some (.adr false (.gpr rd) (pl.ρ sym - (pl.base + BitVec.ofNat 64 (o + 4))))) :=

  ZlibCrc32.Crcz.AdrpProof.adrp_pairs pl hP m hCL o rd sym h
