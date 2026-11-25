-- Prove2me | solution 1 for Poly1305Debian.publicOk_init_update_final_oneshot
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-25T20:35:08.123219+00:00
-- url     : https://prove2.me/submissions/1a66e76e-24ce-41ce-a593-cdf31b3050e4

import Definitions.Def_Poly1305Debian_PlacedObj
import Definitions.Def_Poly1305Debian_Spec
import Theorems.Thm_Poly1305Debian_internalOk_donna_init_update_final_oneshot
import Mathlib.Tactic.IntervalCases
import Definitions.Def_Link_LinkOk

section
section
/-! # Execution by backward chaining, and instruction fetch in the placed libsodium library

`P pl ex` is the placed program with hook table `ex`. No hook has its entry point inside the text
block (`hook_none_in`), so inside the block `Step` is fetch-and-execute. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.PG

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj

abbrev P (pl : Placement) (ex : String → Option (State → State)) : Program :=
  libsodiumDebianOnetimeauthLib.program pl ex

/-! ## Reaching a final state -/

theorem Steps.trans' {p : Program} {a b c : State} (h1 : Steps p a b) (h2 : Steps p b c) :
    Steps p a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact Steps.step h (ih h2)

/-! ## Code loaded, fetch -/

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
theorem code_length : libsodiumDebianOnetimeauthPlacedCode.length = 1800 := by rfl

theorem patched_length (pl : Placement) : (libsodiumDebianOnetimeauthText.patched pl).length = 1800 := by
  unfold CodeBlock.patched
  rw [List.length_flatMap]
  simp only [length_bytesOfWordLE]
  show (List.map (fun _ => 4) (List.range (libsodiumDebianOnetimeauthPlacedCode.length / 4))).sum = 1800
  rw [code_length]; rfl

theorem stub_far {pl : Placement} (hP : libsodiumDebianOnetimeauthLib.Placeable pl) (e : String)
    (he : e ∈ libsodiumDebianOnetimeauthLib.text.externs) : 1800 ≤ (pl.ρ e - pl.base).toNat := by
  have := (hP.text.externs_ok e he).2
  rwa [show libsodiumDebianOnetimeauthLib.text.code.length = 1800 from code_length] at this

/-- No hook has its entry point inside the text block. -/
theorem hook_none_in {pl : Placement} (hP : libsodiumDebianOnetimeauthLib.Placeable pl)
    (ex : String → Option (State → State)) {off : Nat} (hoff : off < 1800) :
    (P pl ex).externAt? (pl.base + BitVec.ofNat 64 off) = none := by
  have e : (pl.base + BitVec.ofNat 64 off - pl.base).toNat = off := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, BitVec.toNat_ofNat]; omega
  simp only [Program.externAt?, Program.hookAtOff?, P, PlacedLib.program, e]
  have h1 : (libsodiumDebianOnetimeauthLib.text.externs.map fun e => (e, (pl.ρ e - pl.base).toNat)).findSome?
      (fun (n, o) => if o == off then ex n else none) = none := by
    rw [List.findSome?_eq_none_iff]
    intro x hx
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp hx
    have := stub_far hP e' he'
    have hne : ((pl.ρ e' - pl.base).toNat == off) = false := by
      simp only [beq_eq_false_iff_ne]; omega
    simp only [hne, Bool.false_eq_true, ite_false]
  have h2 : libsodiumDebianOnetimeauthLib.text.symbols.findSome?
      (fun (n, o) => if o == off then (fun _ => (none : Option (State → State))) n else none) = none := by
    rw [List.findSome?_eq_none_iff]; intro x _; simp
  rw [h1]; simpa using h2

/-- Byte `k < 4` of the word at aligned offset `off` of the placed code. -/
theorem read8_code {pl : Placement} {ex : String → Option (State → State)} {m : Memory}
    (hCL : (P pl ex).CodeLoaded m) {off k : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 1800) (hk : k < 4) :
    m.read8 (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) =
      (libsodiumDebianOnetimeauthText.patchedWord pl off).extractLsb' (8 * k) 8 ∧
    m.perm (pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k) = some Perm.rx := by
  have hl : (P pl ex).code.length = 1800 := patched_length pl
  have h := codeLoaded_cell hCL (off + k) (by omega)
  have ha : pl.base + BitVec.ofNat 64 off + BitVec.ofNat 64 k =
      (P pl ex).base + BitVec.ofNat 64 (off + k) := by
    show _ = pl.base + _
    rw [BitVec.add_assoc, BitVec.ofNat_add]
  rw [ha]
  refine ⟨?_, h.2⟩
  rw [h.1]
  have ht := take4_drop_patched (blk := libsodiumDebianOnetimeauthText) (pl := pl) hal
    (by rw [show libsodiumDebianOnetimeauthText.code = libsodiumDebianOnetimeauthPlacedCode from rfl, code_length]; exact hlen)
  have e1 : (P pl ex).code[off + k]'(by omega) =
      (((libsodiumDebianOnetimeauthText.patched pl).drop off).take 4)[k]'(by
        simp [List.length_take, List.length_drop, patched_length]; omega) := by
    simp only [List.getElem_take, List.getElem_drop]; rfl
  rw [e1]
  simp only [ht, bytesOfWordLE, bytesLE, List.getElem_map, List.getElem_range]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  have : 8 * k + i < 32 := by omega
  simp [hi, this]; omega

theorem fetch_word {pl : Placement} {ex : String → Option (State → State)} {m : Memory}
    (hP : libsodiumDebianOnetimeauthLib.Placeable pl)
    (hCL : (P pl ex).CodeLoaded m) {off : Nat} (hal : off % 4 = 0) (hlen : off + 4 ≤ 1800) :
    (P pl ex).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      decode (libsodiumDebianOnetimeauthText.patchedWord pl off) := by
  have hb4 : pl.base.toNat % 4 = 0 := by
    have := hP.text.base_aligned
    simp [libsodiumDebianOnetimeauthLib, libsodiumDebianOnetimeauthText] at this; omega
  have hnw : pl.base.toNat + 1800 ≤ 2 ^ 64 := by
    have := hP.text.no_wrap
    have hl : libsodiumDebianOnetimeauthText.code.length = 1800 := code_length
    rw [show libsodiumDebianOnetimeauthLib.text = libsodiumDebianOnetimeauthText from rfl, hl] at this
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
  simp only [Program.fetchMem, hook_none_in hP ex (show off < 1800 by omega), Option.isSome_none,
    Bool.false_eq_true, if_false, hpc, ne_eq, not_true_eq_false]
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

theorem patchedWord_plain (pl : Placement) {off : Nat}
    (h : libsodiumDebianOnetimeauthText.relocAt? off = none) :
    libsodiumDebianOnetimeauthText.patchedWord pl off = libsodiumDebianOnetimeauthText.wordAt off := by
  simp [CodeBlock.patchedWord, h]

end Poly1305Debian.PG

end
end

section
section
/-! # The instructions of the public entry points and their `crypto_onetimeauth_poly1305*` counterparts

Each public function is `bti c; b <counterpart>`; each counterpart is
`bti c; adrp xN, implementation; ldr xN, [xN, :lo12:implementation]; ldr xN, [xN, #k]; mov x16, xN; br x16`.
This file decodes all of them under an arbitrary `Placeable` placement. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.PG

open Arm64 Arm64.Obj

/-! ## Decoding by masks -/

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

/-- The three `ldr xN, [xN, #imm]` words (`N = 4, 2, 3`) with their immediate field cleared. -/
def LdrTmpl (A : BitVec 32) (n : BitVec 5) : Prop :=
  (A = 0xf9400084#32 ∧ n = 4#5) ∨ (A = 0xf9400042#32 ∧ n = 2#5) ∨ (A = 0xf9400063#32 ∧ n = 3#5)

theorem decode_ldr (w A : BitVec 32) (n : BitVec 5) (hA : LdrTmpl A n)
    (hK : w &&& 0xffc003ff#32 = A) :
    decode w = some (.ldr .W64 .X64 false (.gpr n)
      (.Offset (.gpr n) (((w.extractLsb' 10 12).zeroExtend 64) <<< 3))) := by
  rcases hA with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ <;>
  · rw [decode]
    simp (config := {maxSteps := 4000000}) (disch := decide) only [beq_false_of_mask hK,
      beq_false_of_mask' hK, Bool.false_and, Bool.or_false, if_false, Bool.false_eq_true]
    have hb := fun i => (show (w.getLsbD i && (0xffc003ff#32 : BitVec 32).getLsbD i) = _ by
      rw [← BitVec.getLsbD_and, hK])
    have hc : (w &&& 0x3f000000#32 == 0x39000000#32) = true := by
      simp only [beq_iff_eq]
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := hb i
      simp only [BitVec.getLsbD_and] at this ⊢
      interval_cases i <;> simp_all
    have e30 : BitVec.extractLsb' 30 2 w = 3#2 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := hb (30 + i)
      simp only [BitVec.getLsbD_extractLsb'] at this ⊢
      interval_cases i <;> simp_all
    have e22 : BitVec.extractLsb' 22 2 w = 1#2 := by
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := hb (22 + i)
      simp only [BitVec.getLsbD_extractLsb'] at this ⊢
      interval_cases i <;> simp_all
    have e0 : BitVec.extractLsb' 0 5 w = n := by
      subst hn
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := hb (0 + i)
      simp only [BitVec.getLsbD_extractLsb'] at this ⊢
      interval_cases i <;> simp_all
    have e5 : BitVec.extractLsb' 5 5 w = n := by
      subst hn
      apply BitVec.eq_of_getLsbD_eq; intro i hi
      have := hb (5 + i)
      simp only [BitVec.getLsbD_extractLsb'] at this ⊢
      interval_cases i <;> simp_all
    rw [if_pos hc, e30, e22, e0, e5]
    subst hn
    rfl

/-! ## `ADRP xN` and `LDR xN, [xN, :lo12:]` words -/

theorem hi_bits32 (D : BitVec 64) (h1 : -(2^32:Int) ≤ D.toInt) (h2 : D.toInt < 2^32) :
    ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32 := by
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

theorem pageOf_add_lo (T : BitVec 64) : pageOf T + (T &&& 0xfff#64) = T := by
  apply BitVec.eq_of_toNat_eq
  have h2 : (T &&& 0xfff#64).toNat = T.toNat % 4096 := by
    rw [BitVec.toNat_and]
    have : (0xfff#64 : BitVec 64).toNat = 2 ^ 12 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
  rw [BitVec.toNat_add, pageOf_toNat, h2]
  have := T.isLt; omega

/-- The three `adrp xN` words (`N = 4, 2, 3`) with their immediate cleared. -/
def AdrpTmpl (W : BitVec 32) (n : BitVec 5) : Prop :=
  (W = 0x90000004#32 ∧ n = 4#5) ∨ (W = 0x90000002#32 ∧ n = 2#5) ∨ (W = 0x90000003#32 ∧ n = 3#5)

theorem adrpW_mask {W : BitVec 32} {n : BitVec 5} (hW : AdrpTmpl W n) (D : BitVec 64) :
    adrpWordOff W D &&& 0x1f000000#32 = 0x10000000#32 := by
  rcases hW with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [adrpWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem adrpW_31 {W : BitVec 32} {n : BitVec 5} (hW : AdrpTmpl W n) (D : BitVec 64) :
    (adrpWordOff W D).getLsbD 31 = true := by
  rcases hW with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [adrpWordOff]

theorem adrpW_rd {W : BitVec 32} {n : BitVec 5} (hW : AdrpTmpl W n) (D : BitVec 64) :
    (adrpWordOff W D).extractLsb' 0 5 = n := by
  rcases hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [adrpWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem adrpW_off {W : BitVec 32} {n : BitVec 5} (hW : AdrpTmpl W n) (D : BitVec 64)
    (hlo : ∀ i, i < 12 → D.getLsbD i = false)
    (hhi : ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32) :
    ((adrpWordOff W D).extractLsb' 5 19 ++ (adrpWordOff W D).extractLsb' 29 2).signExtend 64 <<< 12
      = D := by
  rcases hW with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [adrpWordOff, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend,
      BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getMsbD]
    interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
      first | exact hlo _ (by omega) | exact hhi _ (by omega) (by omega) |
        exact (hhi _ (by omega) (by omega)).symm

theorem decode_adrp {W : BitVec 32} {n : BitVec 5} (hW : AdrpTmpl W n) {P T : BitVec 64}
    (hr : AdrpInRange P T) :
    decode (adrpWord W P T) = some (.adr true (.gpr n) (pageOf T - pageOf P)) := by
  rw [adrpWord, decode_adr_class _ (adrpW_mask hW _), adrpW_31 hW, adrpW_rd hW,
    adrpW_off hW _ (lo_bits T P) (hi_bits32 _ hr.1 hr.2)]
  rcases hW with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rfl

theorem lo12W_mask {A : BitVec 32} {n : BitVec 5} (hA : LdrTmpl A n) (T : BitVec 64) :
    lo12Word 3 A T &&& 0xffc003ff#32 = A := by
  rcases hA with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [lo12Word, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem lo12_imm (A : BitVec 32) (T : BitVec 64) (hal : T &&& 7#64 = 0#64) :
    ((lo12Word 3 A T).extractLsb' 10 12).zeroExtend 64 <<< 3 = T &&& 0xfff#64 := by
  have hb : ∀ i, i < 3 → T.getLsbD i = false := by
    intro i hi
    have := congrArg (fun x => x.getLsbD i) hal
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero] at this
    interval_cases i <;> simp_all
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;> exact hb _ (by omega)

theorem decode_ldr_lo12 {A : BitVec 32} {n : BitVec 5} (hA : LdrTmpl A n) (T : BitVec 64)
    (hal : T &&& 7#64 = 0#64) :
    decode (lo12Word 3 A T) = some (.ldr .W64 .X64 false (.gpr n) (.Offset (.gpr n) (T &&& 0xfff#64))) := by
  rw [decode_ldr _ A n hA (lo12W_mask hA T), lo12_imm A T hal]

end Poly1305Debian.PG

end
end

section
section
/-! # The instruction at each address of the public entry points and their counterparts

Under any `Placeable` placement `pl`, with the placed code loaded. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.PG

open Arm64 Arm64.Obj

/-- The text block. -/
abbrev TX : CodeBlock := libsodiumDebianOnetimeauthText

/-- The relocated word of a relocation that the linker neither relaxes nor retargets. -/
theorem pw_reloc (pl : Placement) {off : Nat} {r : RelocEntry} (hr : TX.relocAt? off = some r)
    (h1 : TX.relaxableAt off = false) (h2 : TX.relaxableAt (off - 4) = false)
    (h3 : r.kind.isGotOrTlsIe = false) (h5 : TX.b2bNext? r = none) :
    TX.patchedWord pl off =
      patchRelocWord r.kind (TX.wordAt off) (pl.base + BitVec.ofNat 64 off) (TX.target pl r) := by
  have hwr : TX.weakRefs = [] := rfl
  have hw : TX.undefWeakBranch pl r = false := by simp [CodeBlock.undefWeakBranch, hwr]
  simp [CodeBlock.patchedWord, hr, CodeBlock.relaxedAt, h1, h2, h3, hw, CodeBlock.relocTarget, h5]

theorem relocTarget_eq (pl : Placement) {off : Nat} {r : RelocEntry} (h5 : TX.b2bNext? r = none) :
    TX.relocTarget pl off r = TX.target pl r := by
  simp [CodeBlock.relocTarget, h5]

theorem reloc_mem {off : Nat} {r : RelocEntry} (hr : TX.relocAt? off = some r) : r ∈ TX.relocs :=
  List.mem_of_find?_eq_some hr

/-- The range condition the placement guarantees for the relocation at `off`. -/
theorem reloc_range {pl : Placement} (hP : libsodiumDebianOnetimeauthLib.Placeable pl) {off : Nat}
    {r : RelocEntry} (hr : TX.relocAt? off = some r) (hoff : r.off = off)
    (h5 : TX.b2bNext? r = none) :
    TX.relocInRange pl r.kind off (pl.base + BitVec.ofNat 64 off) (TX.target pl r) := by
  have h0 : TX.relocInRange pl r.kind r.off (pl.base + BitVec.ofNat 64 r.off)
      (TX.relocTarget pl r.off r) := (hP.text.relocs_ok r (reloc_mem hr)).2.2
  rw [hoff, relocTarget_eq pl h5] at h0
  exact h0

section
variable {pl : Placement} {ex : String → Option (State → State)} {m : Memory}
  (hP : libsodiumDebianOnetimeauthLib.Placeable pl) (hCL : (P pl ex).CodeLoaded m)
include hP hCL

theorem fetch_plain {off : Nat} (hal : off % 4 = 0) (hlen : off + 4 ≤ 1800)
    (h : TX.relocAt? off = none) :
    (P pl ex).fetchMem m (pl.base + BitVec.ofNat 64 off) = decode (TX.wordAt off) := by
  rw [fetch_word hP hCL hal hlen, patchedWord_plain pl h]

/-- A `b` to a symbol of the block at `tgt`, `d = tgt - off` bytes ahead. -/
theorem fetch_b {off tgt : Nat} {r : RelocEntry} (hal : off % 4 = 0) (hlen : off + 4 ≤ 1800)
    (hr : TX.relocAt? off = some r) (h1 : TX.relaxableAt off = false)
    (h2 : TX.relaxableAt (off - 4) = false) (h3 : r.kind.isGotOrTlsIe = false)
    (h5 : TX.b2bNext? r = none) (hk : r.kind = .jump26) (hadd : r.addend = 0)
    (hsym : lookup r.sym TX.symbols = some tgt) (d : BitVec 64)
    (hd : BitVec.ofNat 64 tgt - BitVec.ofNat 64 off = d) :
    (P pl ex).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      decode (branchWord (TX.wordAt off) 0#64 d) := by
  rw [fetch_word hP hCL hal hlen, pw_reloc pl hr h1 h2 h3 h5, hk]
  have ht : TX.target pl r = pl.base + BitVec.ofNat 64 tgt := by
    simp [CodeBlock.target, addSignedAddr, hadd, CodeBlock.resolve, hsym]
  rw [ht]
  simp only [patchRelocWord, branchWord]
  congr 3
  rw [← hd]; bv_omega

/-- An `adrp xN` to a symbol outside the block. -/
theorem fetch_adrp {off : Nat} {r : RelocEntry} {W : BitVec 32} {n : BitVec 5}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 1800)
    (hr : TX.relocAt? off = some r) (hoff : r.off = off) (h1 : TX.relaxableAt off = false)
    (h2 : TX.relaxableAt (off - 4) = false) (h3 : r.kind.isGotOrTlsIe = false)
    (h5 : TX.b2bNext? r = none) (hk : r.kind = .adrpHi21) (hadd : r.addend = 0)
    (hsym : lookup r.sym TX.symbols = none) (hW : TX.wordAt off = W) (hT : AdrpTmpl W n) :
    (P pl ex).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      some (.adr true (.gpr n) (pageOf (pl.ρ r.sym) - pageOf (pl.base + BitVec.ofNat 64 off))) := by
  have ht : TX.target pl r = pl.ρ r.sym := by
    simp [CodeBlock.target, addSignedAddr, hadd, CodeBlock.resolve, hsym]
  have hrg := reloc_range hP hr hoff h5
  rw [hk, ht] at hrg
  rw [fetch_word hP hCL hal hlen, pw_reloc pl hr h1 h2 h3 h5, hk, ht, hW]
  exact decode_adrp hT hrg

/-- An `ldr xN, [xN, :lo12:sym]` for a symbol outside the block. -/
theorem fetch_ldr_lo12 {off : Nat} {r : RelocEntry} {A : BitVec 32} {n : BitVec 5}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ 1800)
    (hr : TX.relocAt? off = some r) (hoff : r.off = off) (h1 : TX.relaxableAt off = false)
    (h2 : TX.relaxableAt (off - 4) = false) (h3 : r.kind.isGotOrTlsIe = false)
    (h5 : TX.b2bNext? r = none) (hk : r.kind = .ldst64Lo12) (hadd : r.addend = 0)
    (hsym : lookup r.sym TX.symbols = none) (hW : TX.wordAt off = A) (hT : LdrTmpl A n) :
    (P pl ex).fetchMem m (pl.base + BitVec.ofNat 64 off) =
      some (.ldr .W64 .X64 false (.gpr n) (.Offset (.gpr n) (pl.ρ r.sym &&& 0xfff#64))) := by
  have ht : TX.target pl r = pl.ρ r.sym := by
    simp [CodeBlock.target, addSignedAddr, hadd, CodeBlock.resolve, hsym]
  have hrg := reloc_range hP hr hoff h5
  rw [hk, ht] at hrg
  rw [fetch_word hP hCL hal hlen, pw_reloc pl hr h1 h2 h3 h5, hk, ht, hW]
  exact decode_ldr_lo12 hT _ hrg

end

end Poly1305Debian.PG

end
end

section
section
/-! # Separation-logic heap algebra

Ported from google-deepmind/code-verification @ 8c8d371f (Apache-2.0),
`arm64-semantics/ProofLib/CoreLemmas.lean` and `ProofLib/SepLogic/Model.lean`: the plain lemmas
about `Heap.Disjoint`, `Heap.union`, `Heap.Matches` and `sepConj`, with ProofLib's custom simp
attributes removed. -/

set_option autoImplicit false

namespace Arm64

namespace SepProp
theorem satisfies_iff {P : SepProp} {m : Memory} :
    (m ⊨ P) ↔ ∃ h : Heap, P.holds h ∧ h.Matches m := Iff.rfl
theorem holds_emp_iff {h : Heap} : (emp : SepProp).holds h ↔ h = Heap.empty := Iff.rfl
theorem holds_sepConj_iff {P Q : SepProp} {h : Heap} :
    (P ∗ Q).holds h ↔
      ∃ h₁ h₂ : Heap, h₁.Disjoint h₂ ∧ h = h₁.union h₂ ∧ P.holds h₁ ∧ Q.holds h₂ := Iff.rfl
end SepProp

theorem holds_pointsTo8_iff {a : BitVec 64} {v : BitVec 8} {h : Heap} :
    (pointsTo8 a v).holds h ↔ h = Heap.singleton a v := Iff.rfl

namespace Heap

theorem Disjoint.symm {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) : h₂.Disjoint h₁ := by
  refine ⟨fun a => ?_, fun γ k => (hd.2.1 γ k).symm, fun γ k => (hd.2.2.1 γ k).symm,
    fun γ k oa v h => hd.2.2.2.1 γ k oa v h.symm, fun a => (hd.2.2.2.2 a).symm⟩
  rcases hd.1 a with h1 | h2 | ⟨b, h1, h2⟩
  · exact Or.inr (Or.inl h1)
  · exact Or.inl h2
  · exact Or.inr (Or.inr ⟨b, h2, h1⟩)

theorem Disjoint.of_phys_left {h₁ h₂ : Heap}
    (ha : h₁.auth = fun _ _ => none := by rfl)
    (hf : h₁.frag = fun _ _ => none := by rfl)
    (hp : ∀ a, h₁.phys a = none ∨ h₂.phys a = none ∨
      ∃ b, h₁.phys a = some (.ro b) ∧ h₂.phys a = some (.ro b))
    (hm : h₁.mapped = fun _ => false := by rfl) :
    h₁.Disjoint h₂ := by
  refine ⟨hp, fun γ k => Or.inl (congrFun (congrFun ha γ) k),
    fun γ k => Or.inl (congrFun (congrFun hf γ) k), fun γ k oa v h => ?_,
    fun a => Or.inl (congrFun hm a)⟩
  rcases h with ⟨h1, _⟩ | ⟨_, h1⟩
  · rw [congrFun (congrFun ha γ) k] at h1; contradiction
  · rw [congrFun (congrFun hf γ) k] at h1; contradiction

@[simp]
theorem disjoint_empty_left (h : Heap) : Heap.empty.Disjoint h :=
  Disjoint.of_phys_left rfl rfl (fun _ => Or.inl rfl)

@[simp]
theorem disjoint_empty_right (h : Heap) : h.Disjoint Heap.empty :=
  (disjoint_empty_left h).symm

@[simp]
theorem union_empty_left (h : Heap) : Heap.empty.union h = h := by
  cases h; rfl

@[simp]
theorem union_empty_right (h : Heap) : h.union Heap.empty = h := by
  apply Heap.ext
  · funext a; dsimp [union, empty]; cases h.phys a <;> rfl
  · funext γ k; dsimp [union, empty]; cases h.auth γ k <;> rfl
  · funext γ k; dsimp [union, empty]; cases h.frag γ k <;> rfl
  · funext a; dsimp [union, empty]; cases h.mapped a <;> rfl

theorem union_comm_of_disjoint {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) :
    h₁.union h₂ = h₂.union h₁ := by
  apply Heap.ext
  · funext a; dsimp [union]
    rcases hd.1 a with h1 | h2 | ⟨b, h1, h2⟩
    · rw [h1]; cases h₂.phys a <;> rfl
    · rw [h2]; cases h₁.phys a <;> rfl
    · rw [h1, h2]
  · funext γ k; dsimp [union]
    rcases hd.2.1 γ k with h1 | h2
    · rw [h1]; cases h₂.auth γ k <;> rfl
    · rw [h2]; cases h₁.auth γ k <;> rfl
  · funext γ k; dsimp [union]
    rcases hd.2.2.1 γ k with h1 | h2
    · rw [h1]; cases h₂.frag γ k <;> rfl
    · rw [h2]; cases h₁.frag γ k <;> rfl
  · funext a; dsimp [union]
    rcases hd.2.2.2.2 a with h1 | h2
    · rw [h1]; cases h₂.mapped a <;> rfl
    · rw [h2]; cases h₁.mapped a <;> rfl

theorem union_assoc (h₁ h₂ h₃ : Heap) :
    (h₁.union h₂).union h₃ = h₁.union (h₂.union h₃) := by
  apply Heap.ext
  · funext a; dsimp [union]; cases h₁.phys a <;> rfl
  · funext γ k; dsimp [union]; cases h₁.auth γ k <;> rfl
  · funext γ k; dsimp [union]; cases h₁.frag γ k <;> rfl
  · funext a; dsimp [union]; cases h₁.mapped a <;> rfl

theorem disjoint_union_left {h₁ h₂ h₃ : Heap} (hd12 : h₁.Disjoint h₂) :
    (h₁.union h₂).Disjoint h₃ ↔ h₁.Disjoint h₃ ∧ h₂.Disjoint h₃ := by
  constructor
  · intro hd
    have hphys1 : ∀ a, h₁.phys a = none ∨ h₃.phys a = none ∨
        ∃ b, h₁.phys a = some (.ro b) ∧ h₃.phys a = some (.ro b) := by
      intro a
      rcases hd.1 a with hu | h3 | ⟨b, hu, h3⟩
      · dsimp [union] at hu; cases h : h₁.phys a <;> simp_all
      · exact Or.inr (Or.inl h3)
      · dsimp [union] at hu
        cases h : h₁.phys a with
        | none => exact Or.inl rfl
        | some c => rw [h] at hu; exact Or.inr (Or.inr ⟨b, hu, h3⟩)
    have hphys2 : ∀ a, h₂.phys a = none ∨ h₃.phys a = none ∨
        ∃ b, h₂.phys a = some (.ro b) ∧ h₃.phys a = some (.ro b) := by
      intro a
      rcases hd.1 a with hu | h3 | ⟨b, hu, h3⟩
      · dsimp [union] at hu; cases h : h₁.phys a <;> simp_all
      · exact Or.inr (Or.inl h3)
      · dsimp [union] at hu
        cases h : h₁.phys a with
        | none => rw [h] at hu; exact Or.inr (Or.inr ⟨b, hu, h3⟩)
        | some c =>
          rw [h] at hu
          rcases hd12.1 a with h1 | h2 | ⟨b', h1, h2⟩
          · rw [h] at h1; contradiction
          · exact Or.inl h2
          · rw [h1] at h; cases h; cases hu; exact Or.inr (Or.inr ⟨b, h2, h3⟩)
    have hauth1 : ∀ γ k, h₁.auth γ k = none ∨ h₃.auth γ k = none := by
      intro γ k
      rcases hd.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.auth γ k <;> simp_all
      · exact Or.inr h3
    have hauth2 : ∀ γ k, h₂.auth γ k = none ∨ h₃.auth γ k = none := by
      intro γ k
      rcases hd.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.auth γ k <;> simp_all
      · exact Or.inr h3
    have hfrag1 : ∀ γ k, h₁.frag γ k = none ∨ h₃.frag γ k = none := by
      intro γ k
      rcases hd.2.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.frag γ k <;> simp_all
      · exact Or.inr h3
    have hfrag2 : ∀ γ k, h₂.frag γ k = none ∨ h₃.frag γ k = none := by
      intro γ k
      rcases hd.2.2.1 γ k with hu | h3
      · dsimp [union] at hu; cases h : h₁.frag γ k <;> simp_all
      · exact Or.inr h3
    have hcompat1 : ∀ γ k oa v,
        ((h₁.auth γ k = some oa ∧ h₃.frag γ k = some v) ∨
         (h₃.auth γ k = some oa ∧ h₁.frag γ k = some v)) → oa = some v := by
      intro γ k oa v h
      apply hd.2.2.2.1 γ k oa v
      rcases h with ⟨ha, hf⟩ | ⟨ha, hf⟩
      ·exact Or.inl ⟨by dsimp [union]; rw [ha], hf⟩
      · exact Or.inr ⟨ha, by dsimp [union]; rw [hf]⟩
    have hcompat2 : ∀ γ k oa v,
        ((h₂.auth γ k = some oa ∧ h₃.frag γ k = some v) ∨
         (h₃.auth γ k = some oa ∧ h₂.frag γ k = some v)) → oa = some v := by
      intro γ k oa v h
      apply hd.2.2.2.1 γ k oa v
      rcases h with ⟨ha, hf⟩ | ⟨ha, hf⟩
      · rcases hd12.2.1 γ k with h1 | h2
        · exact Or.inl ⟨by dsimp [union]; rw [h1, ha], hf⟩
        · rw [ha] at h2; contradiction
      · rcases hd12.2.2.1 γ k with h1 | h2
        · exact Or.inr ⟨ha, by dsimp [union]; rw [h1, hf]⟩
        · rw [hf] at h2; contradiction
    have hmapped1 : ∀ a, h₁.mapped a = false ∨ h₃.mapped a = false := by
      intro a
      rcases hd.2.2.2.2 a with hu | h3
      · dsimp [union] at hu; cases h : h₁.mapped a <;> simp_all
      · exact Or.inr h3
    have hmapped2 : ∀ a, h₂.mapped a = false ∨ h₃.mapped a = false := by
      intro a
      rcases hd.2.2.2.2 a with hu | h3
      · dsimp [union] at hu; cases h : h₁.mapped a <;> simp_all
      · exact Or.inr h3
    exact ⟨⟨hphys1, hauth1, hfrag1, hcompat1, hmapped1⟩, ⟨hphys2, hauth2, hfrag2, hcompat2, hmapped2⟩⟩
  · rintro ⟨hd1, hd2⟩
    refine ⟨fun a => ?_, fun γ k => ?_, fun γ k => ?_, fun γ k oa v h => ?_, fun a => ?_⟩
    · dsimp [union]
      cases h : h₁.phys a with
      | none => exact hd2.1 a
      | some c =>
        rcases hd1.1 a with h1 | h3 | ⟨b, h1, h3⟩
        · rw [h] at h1; contradiction
        · exact Or.inr (Or.inl h3)
        · rw [h] at h1; exact Or.inr (Or.inr ⟨b, h1, h3⟩)
    · dsimp [union]
      cases h : h₁.auth γ k with
      | none => exact hd2.2.1 γ k
      | some oa =>
        rcases hd1.2.1 γ k with h1 | h3
        · rw [h] at h1; contradiction
        · exact Or.inr h3
    · dsimp [union]
      cases h : h₁.frag γ k with
      | none => exact hd2.2.2.1 γ k
      | some v =>
        rcases hd1.2.2.1 γ k with h1 | h3
        · rw [h] at h1; contradiction
        · exact Or.inr h3
    · rcases h with ⟨ha, hf⟩ | ⟨ha, hf⟩
      · dsimp [union] at ha
        cases h1 : h₁.auth γ k with
        | none =>
          rw [h1] at ha
          exact hd2.2.2.2.1 γ k oa v (Or.inl ⟨ha, hf⟩)
        | some oa' =>
          rw [h1] at ha; cases ha
          exact hd1.2.2.2.1 γ k oa v (Or.inl ⟨h1, hf⟩)
      · dsimp [union] at hf
        cases h1 : h₁.frag γ k with
        | none =>
          rw [h1] at hf
          exact hd2.2.2.2.1 γ k oa v (Or.inr ⟨ha, hf⟩)
        | some v' =>
          rw [h1] at hf; cases hf
          exact hd1.2.2.2.1 γ k oa v (Or.inr ⟨ha, h1⟩)
    · dsimp [union]
      cases h : h₁.mapped a with
      | false => exact hd2.2.2.2.2 a
      | true =>
        rcases hd1.2.2.2.2 a with h1 | h3
        · rw [h] at h1; contradiction
        · exact Or.inr h3

theorem disjoint_union_right {h₁ h₂ h₃ : Heap} (hd23 : h₂.Disjoint h₃) :
    h₁.Disjoint (h₂.union h₃) ↔ h₁.Disjoint h₂ ∧ h₁.Disjoint h₃ := by
  constructor
  · intro hd
    have hd' := (disjoint_union_left hd23).mp hd.symm
    exact ⟨hd'.1.symm, hd'.2.symm⟩
  · rintro ⟨hd1, hd2⟩
    exact ((disjoint_union_left hd23).mpr ⟨hd1.symm, hd2.symm⟩).symm

theorem GhostValid.of_union_left {h₁ h₂ : Heap} (hv : (h₁.union h₂).GhostValid) :
    h₁.GhostValid := by
  rcases hv with ⟨b, hb⟩
  refine ⟨b, fun γ hγ k => ?_⟩
  have ⟨hau, hfu⟩ := hb γ hγ k
  dsimp [Heap.union] at hau hfu
  constructor
  · cases h : h₁.auth γ k with
    | none => rfl
    | some _ => rw [h] at hau; contradiction
  · cases h : h₁.frag γ k with
    | none => rfl
    | some _ => rw [h] at hfu; contradiction

theorem Matches.of_union_left {h₁ h₂ : Heap} {m : Memory}
    (hm : (h₁.union h₂).Matches m) :
    h₁.Matches m :=
  ⟨fun a c h1 => hm.1 a c (by dsimp [Heap.union]; rw [h1]),
    GhostValid.of_union_left hm.2.1,
    fun a h1 => hm.2.2 a (by dsimp [Heap.union]; rw [h1, Bool.true_or])⟩

end Heap











theorem sepConj_comm (P Q : SepProp) : (P ∗ Q) = (Q ∗ P) := by
  ext h
  simp only [SepProp.holds_sepConj_iff]
  constructor
  · rintro ⟨h₁, h₂, hd, rfl, hp, hq⟩
    exact ⟨h₂, h₁, hd.symm, Heap.union_comm_of_disjoint hd, hq, hp⟩
  · rintro ⟨h₁, h₂, hd, rfl, hq, hp⟩
    exact ⟨h₂, h₁, hd.symm, Heap.union_comm_of_disjoint hd, hp, hq⟩



@[simp]
theorem sepConj_assoc (P Q R : SepProp) : ((P ∗ Q) ∗ R) = (P ∗ (Q ∗ R)) := by
  ext h
  simp only [SepProp.holds_sepConj_iff]
  constructor
  · rintro ⟨h₁₂, h₃, hd12_3, rfl, ⟨h₁, h₂, hd1_2, rfl, hp, hq⟩, hr⟩
    have ⟨hd1_3, hd2_3⟩ := (Heap.disjoint_union_left hd1_2).mp hd12_3
    exact ⟨h₁, h₂.union h₃, (Heap.disjoint_union_right hd2_3).mpr ⟨hd1_2, hd1_3⟩,
      Heap.union_assoc h₁ h₂ h₃, hp, ⟨h₂, h₃, hd2_3, rfl, hq, hr⟩⟩
  · rintro ⟨h₁, h₂₃, hd1_23, rfl, hp, ⟨h₂, h₃, hd2_3, rfl, hq, hr⟩⟩
    have ⟨hd1_2, hd1_3⟩ := (Heap.disjoint_union_right hd2_3).mp hd1_23
    exact ⟨h₁.union h₂, h₃, (Heap.disjoint_union_left hd1_2).mpr ⟨hd1_3, hd2_3⟩,
      (Heap.union_assoc h₁ h₂ h₃).symm, ⟨h₁, h₂, hd1_2, rfl, hp, hq⟩, hr⟩

instance instAssociativeSepConj : Std.Associative SepProp.sepConj where
  assoc := sepConj_assoc

instance instCommutativeSepConj : Std.Commutative SepProp.sepConj where
  comm := sepConj_comm

theorem Satisfies.of_eq {P Q : SepProp} {m : Memory}
    (h : m ⊨ P) (heq : P = Q := by ac_rfl) : m ⊨ Q :=
  heq ▸ h

@[simp]
theorem emp_sepConj (P : SepProp) : (SepProp.emp ∗ P) = P := by
  ext h
  simp only [SepProp.holds_sepConj_iff, SepProp.holds_emp_iff]
  constructor
  · rintro ⟨h₁, h₂, _, rfl, rfl, hp⟩
    simpa using hp
  · intro hp
    exact ⟨Heap.empty, h, Heap.disjoint_empty_left h, (Heap.union_empty_left h).symm, rfl, hp⟩

@[simp]
theorem sepConj_emp (P : SepProp) : (P ∗ SepProp.emp) = P := by
  rw [sepConj_comm, emp_sepConj]


end Arm64

end
end

section
section
/-! # Byte-slice ownership: reads, writes, splits

Plain-Lean replacements for the parts of DeepMind's ProofLib (google-deepmind/code-verification
@ 8c8d371f, Apache-2.0, `ProofLib/SepLogic/Bytes.lean`) that the x25519 ladder proofs use:
`a ↦ₛ bs` owns `bs` at `a`; a store to an owned byte updates the list; `pointsTo64` and `memRegion`
are byte slices. -/

set_option autoImplicit false

namespace Arm64

theorem pointsToBytes_cons (a : BitVec 64) (b : BitVec 8) (bs : List (BitVec 8)) :
    (a ↦ₛ (b :: bs)) = (a ↦₈ b) ∗ ((a + 1#64) ↦ₛ bs) := rfl
theorem pointsToBytes_nil (a : BitVec 64) : (a ↦ₛ ([] : List (BitVec 8))) = emp := rfl

namespace Heap

theorem rw_phys_right_none {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) {x : BitVec 64} {b : BitVec 8}
    (hx : h₁.phys x = some (.rw b)) : h₂.phys x = none := by
  rcases hd.1 x with h | h | ⟨b', h1, _⟩
  · rw [hx] at h; cases h
  · exact h
  · rw [hx] at h1; cases h1

theorem rw_phys_left_none {h₁ h₂ : Heap} (hd : h₁.Disjoint h₂) {x : BitVec 64} {b : BitVec 8}
    (hx : h₂.phys x = some (.rw b)) : h₁.phys x = none :=
  rw_phys_right_none hd.symm hx

end Heap

/-! ## Memory facts about `write8` -/

namespace Memory

end Memory

namespace Heap

end Heap

/-! ## Byte slices as heaps -/

theorem bytes_phys : ∀ {a : BitVec 64} {bs : List (BitVec 8)} {h : Heap},
    (a ↦ₛ bs).holds h → ∀ (j : Nat) (hj : j < bs.length),
      h.phys (a + BitVec.ofNat 64 j) = some (.rw bs[j])
  | _, [], _, _, j, hj => by simp at hj
  | a, b :: bs, h, hh, j, hj => by
    obtain ⟨h1, h2, hd, rfl, h1e, h2h⟩ := SepProp.holds_sepConj_iff.mp hh
    rw [holds_pointsTo8_iff] at h1e; subst h1e
    cases j with
    | zero => simp [Heap.union, Heap.singleton]
    | succ j =>
      have ih := bytes_phys h2h j (by simp at hj; omega)
      have ha : a + BitVec.ofNat 64 (j + 1) = a + 1#64 + BitVec.ofNat 64 j := by
        rw [BitVec.add_assoc]; congr 1; bv_omega
      have hne : a + 1#64 + BitVec.ofNat 64 j ≠ a := by
        intro he
        have := Heap.rw_phys_left_none hd ih
        rw [he] at this; simp [Heap.singleton] at this
      rw [ha]
      simp only [Heap.union, Heap.singleton, hne, if_false, ih, List.getElem_cons_succ]

/-! ## Satisfaction-level reads and writes -/

theorem sat_bytes_read {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    (hs : m ⊨ (a ↦ₛ bs) ∗ F) (j : Nat) (hj : j < bs.length) :
    m.read8 (a + BitVec.ofNat 64 j) = bs[j] ∧ m.perm (a + BitVec.ofNat 64 j) = some Perm.rw ∧
      m.isLazyFree (a + BitVec.ofNat 64 j) = false := by
  obtain ⟨h, hh, hm⟩ := SepProp.satisfies_iff.mp hs
  obtain ⟨h1, h2, hd, rfl, h1h, _⟩ := SepProp.holds_sepConj_iff.mp hh
  have hp := bytes_phys h1h j hj
  have := (Heap.Matches.of_union_left hm).1 _ _ hp
  exact this

/-! ## Splitting byte slices -/

theorem pointsToBytes_append (a : BitVec 64) (xs ys : List (BitVec 8)) :
    (a ↦ₛ (xs ++ ys)) = (a ↦ₛ xs) ∗ ((a + BitVec.ofNat 64 xs.length) ↦ₛ ys) := by
  induction xs generalizing a with
  | nil => simp [pointsToBytes_nil]
  | cons x xs ih =>
    rw [List.cons_append, pointsToBytes_cons, pointsToBytes_cons, ih, sepConj_assoc]
    have e : a + 1#64 + BitVec.ofNat 64 xs.length = a + BitVec.ofNat 64 (x :: xs).length := by
      simp only [List.length_cons]; rw [BitVec.add_assoc]; congr 1; bv_omega
    rw [e]

/-- Unpack a 64-bit word into its 8 little-endian bytes. -/
def unpack64 (v : BitVec 64) : List (BitVec 8) :=
  [v.extractLsb' 0 8, v.extractLsb' 8 8, v.extractLsb' 16 8, v.extractLsb' 24 8,
   v.extractLsb' 32 8, v.extractLsb' 40 8, v.extractLsb' 48 8, v.extractLsb' 56 8]

@[simp] theorem unpack64_length (v : BitVec 64) : (unpack64 v).length = 8 := rfl

theorem pointsTo64_eq_bytes (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦ₛ unpack64 v) := by
  simp only [pointsTo64, unpack64, pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_zero]
  have h2 : a + 1#64 + 1#64 = a + 2#64 := by bv_omega
  have h3 : a + 2#64 + 1#64 = a + 3#64 := by bv_omega
  have h4 : a + 3#64 + 1#64 = a + 4#64 := by bv_omega
  have h5 : a + 4#64 + 1#64 = a + 5#64 := by bv_omega
  have h6 : a + 5#64 + 1#64 = a + 6#64 := by bv_omega
  have h7 : a + 6#64 + 1#64 = a + 7#64 := by bv_omega
  rw [h2, h3, h4, h5, h6, h7]

end Arm64

end
end

section
section
/-! # Regions, existentials and pure facts

`memRegion a n` (a stack frame) is a byte slice of length `n` with unknown contents; pure
assertions and separating existentials move in and out of `⊨`. -/

set_option autoImplicit false

namespace Arm64

theorem pure_sepConj_holds {φ : Prop} {P : SepProp} {h : Heap} :
    (⌜φ⌝ ∗ P).holds h ↔ φ ∧ P.holds h := by
  constructor
  · intro hh
    obtain ⟨h₁, h₂, _, rfl, ⟨rfl, hφ⟩, hp⟩ := SepProp.holds_sepConj_iff.mp hh
    exact ⟨hφ, by rw [Heap.union_empty_left]; exact hp⟩
  · rintro ⟨hφ, hp⟩
    exact SepProp.holds_sepConj_iff.mpr ⟨Heap.empty, h, Heap.disjoint_empty_left h,
      (Heap.union_empty_left h).symm, ⟨rfl, hφ⟩, hp⟩

theorem sat_pure_sep {m : Memory} {φ : Prop} {P : SepProp} : (m ⊨ ⌜φ⌝ ∗ P) ↔ φ ∧ (m ⊨ P) := by
  constructor
  · intro hs
    obtain ⟨h, hh, hm⟩ := SepProp.satisfies_iff.mp hs
    have := pure_sepConj_holds.mp hh
    exact ⟨this.1, SepProp.satisfies_iff.mpr ⟨h, this.2, hm⟩⟩
  · rintro ⟨hφ, hs⟩
    obtain ⟨h, hh, hm⟩ := SepProp.satisfies_iff.mp hs
    exact SepProp.satisfies_iff.mpr ⟨h, pure_sepConj_holds.mpr ⟨hφ, hh⟩, hm⟩

/-! ## Byte-slice heaps carry no ghost state and nothing outside the slice -/

end Arm64

end
end

section
section
/-! # 64-bit cells and byte reads: values and permissions from ownership -/

set_option autoImplicit false

namespace Arm64

theorem concat8_extract (v : BitVec 64) :
    v.extractLsb' 56 8 ++ v.extractLsb' 48 8 ++ v.extractLsb' 40 8 ++ v.extractLsb' 32 8 ++
      v.extractLsb' 24 8 ++ v.extractLsb' 16 8 ++ v.extractLsb' 8 8 ++ v.extractLsb' 0 8 = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

theorem canRead_of {m : Memory} : ∀ {x : BitVec 64} {n : Nat},
    (∀ i < n, (m.perm (x + BitVec.ofNat 64 i)).r = true ∧
      m.isLazyFree (x + BitVec.ofNat 64 i) = false) → m.canRead x n = true
  | _, 0, _ => rfl
  | x, n + 1, h => by
    have h0 := h 0 (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    have ih := canRead_of (x := x + 1#64) (n := n) (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show x + BitVec.ofNat 64 (i + 1) = x + 1#64 + BitVec.ofNat 64 i by
        rw [BitVec.add_assoc]; congr 1; bv_omega] at this)
    simp only [Memory.canRead, Memory.allPerm, Memory.allNoLazyFree] at ih ⊢
    simp only [Bool.and_eq_true] at ih
    simp [h0.1, h0.2, ih.1, ih.2]

theorem canWrite_of {m : Memory} : ∀ {x : BitVec 64} {n : Nat},
    (∀ i < n, m.perm (x + BitVec.ofNat 64 i) = some Perm.rw) → m.canWrite x n = true
  | _, 0, _ => rfl
  | x, n + 1, h => by
    have h0 := h 0 (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    have ih := canWrite_of (x := x + 1#64) (n := n) (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [show x + BitVec.ofNat 64 (i + 1) = x + 1#64 + BitVec.ofNat 64 i by
        rw [BitVec.add_assoc]; congr 1; bv_omega] at this)
    simp only [Memory.canWrite, Memory.allPerm] at ih ⊢
    simp [h0, ih, Perm.rw]

/-- Byte `i` of `unpack64 v`. -/
theorem unpack64_getElem (v : BitVec 64) (i : Nat) (hi : i < 8) :
    (unpack64 v)[i]'(by simp; omega) = v.extractLsb' (8 * i) 8 := by
  interval_cases i <;> rfl

theorem sat64_byte {m : Memory} {a v : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦₆₄ v) ∗ F)
    (i : Nat) (hi : i < 8) :
    m.read8 (a + BitVec.ofNat 64 i) = v.extractLsb' (8 * i) 8 ∧
      m.perm (a + BitVec.ofNat 64 i) = some Perm.rw ∧
      m.isLazyFree (a + BitVec.ofNat 64 i) = false := by
  rw [pointsTo64_eq_bytes] at hs
  have := sat_bytes_read hs i (by simp; omega)
  rwa [unpack64_getElem v i hi] at this

theorem sat64_read {m : Memory} {a v : BitVec 64} {F : SepProp} (hs : m ⊨ (a ↦₆₄ v) ∗ F) :
    m.read64 a = v ∧ m.canRead a 8 = true ∧ m.canWrite a 8 = true := by
  refine ⟨?_, canRead_of (fun i hi => ?_), canWrite_of (fun i hi => (sat64_byte hs i hi).2.1)⟩
  · have h0 := (sat64_byte hs 0 (by omega)).1
    have h1 := (sat64_byte hs 1 (by omega)).1
    have h2 := (sat64_byte hs 2 (by omega)).1
    have h3 := (sat64_byte hs 3 (by omega)).1
    have h4 := (sat64_byte hs 4 (by omega)).1
    have h5 := (sat64_byte hs 5 (by omega)).1
    have h6 := (sat64_byte hs 6 (by omega)).1
    have h7 := (sat64_byte hs 7 (by omega)).1
    simp only [BitVec.ofNat_eq_ofNat, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7
    simp only [Memory.read64]
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
    exact concat8_extract v
  · have := sat64_byte hs i hi
    rw [this.2.1]; exact ⟨rfl, this.2.2⟩

end Arm64

end
end

section
section
/-! # 64-bit reads and writes inside owned byte lists; stack regions

`memRegion_split`, `memRegion_merge`, `pack64` and `unpack64_pack64` are copied from the x25519
`G` tree (`Solutions/X25519DalekField/G/Mem.lean`, `Solutions/X25519DalekEdwards/Dbl/Frame.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.PG

open Poly1305Libsodium (u64At rLimb hLimb limbVal StateOk hibit blocksAcc bytesIn MemzeroOk finishTag)

open Arm64 Arm64.Obj Poly1305Boringssl

end Poly1305Debian.PG

end
end

section
section
/-! # A public entry point through `implementation`: the compose rule

Layout-independent: the entry `e`, the counterpart `c`, the pointer slot `I`, the table `Tb`, its
offset `k`, the loaded target `fn` and the scratch register `xN` are parameters. `wrap_compose`
turns a contract of the target (`subroutine_ok P fn spec`) into the contract of the entry point with
an extra resource `D` (the library's data, holding the pointer and the table) lent to the call and
handed back. -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.PG

open Arm64 Arm64.Obj

/-! ## The instructions on a general state -/

section exec
variable {svc : State → State}

theorem ex_hint (s : State) : execInstWithSvc svc (.hint 0x22#7) s = s.advancePC := by
  simp [execInstWithSvc]

theorem ex_b (s : State) (off : BitVec 64) :
    execInstWithSvc svc (.b off) s = s.setPC (s.pc + off) := rfl

theorem ex_adrp (s : State) (rd : BitVec 5) (off : BitVec 64) :
    execInstWithSvc svc (.adr true (.gpr rd) off) s =
      (s.writeReg64 (.gpr rd) ((s.pc &&& 0xfffffffffffff000#64) + off)).advancePC := rfl

theorem ex_br (s : State) (n : BitVec 5) :
    execInstWithSvc svc (.br (.gpr n)) s = s.setPC (s.readReg64 (.gpr n)) := rfl

theorem ex_ldr (s : State) (a n : BitVec 5) (_ha : a ≠ 31#5) (off : BitVec 64)
    (hr : s.mem.canRead (s.readReg64 (.gpr n) + off) 8 = true) :
    execInstWithSvc svc (.ldr .W64 .X64 false (.gpr a) (.Offset (.gpr n) off)) s =
      (s.writeReg64 (.gpr a) (s.mem.read64 (s.readReg64 (.gpr n) + off))).advancePC := by
  simp [execInstWithSvc, checkAddrSPAligned, checkRegSPAligned, evalAddrMode, hr, Memory.readSized,
    AddrMode.baseReg, State.writeReg]

theorem ex_mov (s : State) (n : BitVec 5) :
    execInstWithSvc svc (.logicalShift .W64 .ORR (.gpr 16#5) .xzr (.gpr n) .LSL 0) s =
      (s.writeReg64 (.gpr 16#5) (s.readReg64 (.gpr n))).advancePC := by
  simp [execInstWithSvc, evalLogical, shiftVal, State.readReg, State.writeReg, State.readReg64,
    shift64]

end exec

theorem readReg_write_ne (s : State) (i j : BitVec 5) (v : BitVec 64) (h : i ≠ j) :
    (s.writeReg64 (.gpr j) v).readReg64 (.gpr i) = s.readReg64 (.gpr i) := by
  by_cases hj : j = 31#5
  · subst hj; simp [State.writeReg64, State.readReg64]
  · by_cases hi : i = 31#5
    · simp [State.readReg64, hi]
    · simp [State.writeReg64, State.readReg64, hj, hi, RegFile.read, RegFile.write, h]

theorem readReg_write_same (s : State) (j : BitVec 5) (v : BitVec 64) (hj : j ≠ 31#5) :
    (s.writeReg64 (.gpr j) v).readReg64 (.gpr j) = v := by
  simp [State.writeReg64, State.readReg64, hj, RegFile.read, RegFile.write]

theorem readReg_adv (s : State) (i : BitVec 5) : s.advancePC.readReg64 (.gpr i) = s.readReg64 (.gpr i) :=
  rfl

theorem readReg_setPC (s : State) (p : BitVec 64) (i : BitVec 5) :
    (s.setPC p).readReg64 (.gpr i) = s.readReg64 (.gpr i) := rfl

/-! ## The state after the eight instructions -/

/-- The state after `bti; b c; bti; adrp xN; ldr xN; ldr xN; mov x16, xN; br x16`. -/
def wState (s0 : State) (c I Tb fn : BitVec 64) (N : BitVec 5) : State :=
  let a := (s0.advancePC.setPC c).advancePC
  let b := (a.writeReg64 (.gpr N) (pageOf I)).advancePC
  let c' := (b.writeReg64 (.gpr N) Tb).advancePC
  let d := (c'.writeReg64 (.gpr N) fn).advancePC
  let e := (d.writeReg64 (.gpr 16#5) fn).advancePC
  e.setPC fn

theorem wState_reg (s0 : State) (c I Tb fn : BitVec 64) (N i : BitVec 5) (h16 : i ≠ 16#5)
    (hN : i ≠ N) : (wState s0 c I Tb fn N).readReg64 (.gpr i) = s0.readReg64 (.gpr i) := by
  unfold wState
  simp only [readReg_setPC, readReg_adv, readReg_write_ne _ _ _ _ h16, readReg_write_ne _ _ _ _ hN]

theorem wState_sp (s0 : State) (c I Tb fn : BitVec 64) (N : BitVec 5) :
    (wState s0 c I Tb fn N).sp = s0.sp := by
  simp [wState, State.writeReg64, State.setPC, State.advancePC]

theorem wState_vregs (s0 : State) (c I Tb fn : BitVec 64) (N : BitVec 5) :
    (wState s0 c I Tb fn N).vregs = s0.vregs := by
  simp [wState, State.writeReg64, State.setPC, State.advancePC]

theorem wState_mem (s0 : State) (c I Tb fn : BitVec 64) (N : BitVec 5) :
    (wState s0 c I Tb fn N).mem = s0.mem := by
  simp [wState, State.writeReg64, State.setPC, State.advancePC]

theorem wState_status (s0 : State) (c I Tb fn : BitVec 64) (N : BitVec 5) :
    (wState s0 c I Tb fn N).status = s0.status := by
  simp [wState, State.writeReg64, State.setPC, State.advancePC]

theorem wState_pc (s0 : State) (c I Tb fn : BitVec 64) (N : BitVec 5) :
    (wState s0 c I Tb fn N).pc = fn := by
  simp [wState, State.setPC]

/-- The fetch facts of one entry point at `e` whose counterpart is at `c`. -/
structure WrapCode (P : Program) (e c d I k : BitVec 64) (N : BitVec 5) : Prop where
  b_ok : e + 4#64 + d = c
  f0 : ∀ m, P.CodeLoaded m → P.fetchMem m e = some (.hint 0x22#7)
  f1 : ∀ m, P.CodeLoaded m → P.fetchMem m (e + 4#64) = some (.b d)
  f2 : ∀ m, P.CodeLoaded m → P.fetchMem m c = some (.hint 0x22#7)
  f3 : ∀ m, P.CodeLoaded m → P.fetchMem m (c + 4#64) =
    some (.adr true (.gpr N) (pageOf I - pageOf (c + 4#64)))
  f4 : ∀ m, P.CodeLoaded m → P.fetchMem m (c + 8#64) =
    some (.ldr .W64 .X64 false (.gpr N) (.Offset (.gpr N) (I &&& 0xfff#64)))
  f5 : ∀ m, P.CodeLoaded m → P.fetchMem m (c + 12#64) =
    some (.ldr .W64 .X64 false (.gpr N) (.Offset (.gpr N) k))
  f6 : ∀ m, P.CodeLoaded m → P.fetchMem m (c + 16#64) =
    some (.logicalShift .W64 .ORR (.gpr 16#5) .xzr (.gpr N) .LSL 0)
  f7 : ∀ m, P.CodeLoaded m → P.fetchMem m (c + 20#64) = some (.br (.gpr 16#5))

/-- Running the eight instructions: a `Steps` from the entry state to `wState`. -/
theorem wrap_steps {P : Program} {e c d I k Tb fn : BitVec 64} {N : BitVec 5}
    (hW : WrapCode P e c d I k N) (hN31 : N ≠ 31#5) {s0 : State}
    (hpc : s0.pc = e) (hrun : s0.status = .Running) (hCL : P.CodeLoaded s0.mem)
    (hrI : s0.mem.read64 I = Tb) (hcI : s0.mem.canRead I 8 = true)
    (hrT : s0.mem.read64 (Tb + k) = fn) (hcT : s0.mem.canRead (Tb + k) 8 = true) :
    Steps P s0 (wState s0 c I Tb fn N) := by
  -- 1: `bti c`
  refine Steps.step (Step.exec hrun (by rw [hpc]; exact hW.f0 _ hCL)) ?_
  rw [show P.evalInst (.hint 0x22#7) s0 = s0.advancePC from ex_hint s0]
  -- 2: `b c`
  set s1 := s0.advancePC with hs1
  have p1 : s1.pc = e + 4#64 := by rw [hs1, State.advancePC]; simp [hpc]
  refine Steps.step (Step.exec (s := s1) hrun (by rw [p1]; exact hW.f1 _ hCL)) ?_
  rw [show P.evalInst (.b d) s1 = s1.setPC c by
    show execInstWithSvc _ _ _ = _
    rw [ex_b, p1, hW.b_ok]]
  -- 3: `bti c`
  set s2 := s1.setPC c with hs2
  refine Steps.step (Step.exec (s := s2) hrun (hW.f2 _ hCL)) ?_
  rw [show P.evalInst (.hint 0x22#7) s2 = s2.advancePC from ex_hint s2]
  -- 4: `adrp xN, I`
  set s3 := s2.advancePC with hs3
  have p3 : s3.pc = c + 4#64 := rfl
  refine Steps.step (Step.exec (s := s3) hrun (by rw [p3]; exact hW.f3 _ hCL)) ?_
  rw [show P.evalInst (.adr true (.gpr N) (pageOf I - pageOf (c + 4#64))) s3 =
      (s3.writeReg64 (.gpr N) (pageOf I)).advancePC by
    show execInstWithSvc _ _ _ = _
    rw [ex_adrp, p3]
    congr 2
    rw [show (c + 4#64) &&& 0xfffffffffffff000#64 = pageOf (c + 4#64) from rfl]; bv_omega]
  -- 5: `ldr xN, [xN, :lo12:I]`
  set s4 := (s3.writeReg64 (.gpr N) (pageOf I)).advancePC with hs4
  have x4 : s4.readReg64 (.gpr N) = pageOf I := readReg_write_same _ _ _ hN31
  have m4 : s4.mem = s0.mem := rfl
  refine Steps.step (Step.exec (s := s4) hrun (by
    show P.fetchMem s0.mem (c + 4#64 + 4#64) = _
    rw [show c + 4#64 + 4#64 = c + 8#64 by bv_omega]; exact hW.f4 _ hCL)) ?_
  rw [show P.evalInst (.ldr .W64 .X64 false (.gpr N) (.Offset (.gpr N) (I &&& 0xfff#64))) s4 =
      (s4.writeReg64 (.gpr N) Tb).advancePC by
    show execInstWithSvc _ _ _ = _
    rw [ex_ldr _ _ _ hN31 _ (by rw [x4, pageOf_add_lo, m4]; exact hcI), x4, pageOf_add_lo, m4, hrI]]
  -- 6: `ldr xN, [xN, #k]`
  set s5 := (s4.writeReg64 (.gpr N) Tb).advancePC with hs5
  have x5 : s5.readReg64 (.gpr N) = Tb := readReg_write_same _ _ _ hN31
  have m5 : s5.mem = s0.mem := rfl
  refine Steps.step (Step.exec (s := s5) hrun (by
    show P.fetchMem s0.mem (c + 4#64 + 4#64 + 4#64) = _
    rw [show c + 4#64 + 4#64 + 4#64 = c + 12#64 by bv_omega]; exact hW.f5 _ hCL)) ?_
  rw [show P.evalInst (.ldr .W64 .X64 false (.gpr N) (.Offset (.gpr N) k)) s5 =
      (s5.writeReg64 (.gpr N) fn).advancePC by
    show execInstWithSvc _ _ _ = _
    rw [ex_ldr _ _ _ hN31 _ (by rw [x5, m5]; exact hcT), x5, m5, hrT]]
  -- 7: `mov x16, xN`
  set s6 := (s5.writeReg64 (.gpr N) fn).advancePC with hs6
  have x6 : s6.readReg64 (.gpr N) = fn := readReg_write_same _ _ _ hN31
  refine Steps.step (Step.exec (s := s6) hrun (by
    show P.fetchMem s0.mem (c + 4#64 + 4#64 + 4#64 + 4#64) = _
    rw [show c + 4#64 + 4#64 + 4#64 + 4#64 = c + 16#64 by bv_omega]; exact hW.f6 _ hCL)) ?_
  rw [show P.evalInst (.logicalShift .W64 .ORR (.gpr 16#5) .xzr (.gpr N) .LSL 0) s6 =
      (s6.writeReg64 (.gpr 16#5) fn).advancePC by
    show execInstWithSvc _ _ _ = _
    rw [ex_mov, x6]]
  -- 8: `br x16`
  set s7 := (s6.writeReg64 (.gpr 16#5) fn).advancePC with hs7
  have x7 : s7.readReg64 (.gpr 16#5) = fn := by
    rw [hs7, readReg_adv]; exact readReg_write_same _ _ _ (by decide)
  refine Steps.step (Step.exec (s := s7) hrun (by
    show P.fetchMem s0.mem (c + 4#64 + 4#64 + 4#64 + 4#64 + 4#64) = _
    rw [show c + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 = c + 20#64 by bv_omega]; exact hW.f7 _ hCL)) ?_
  rw [show P.evalInst (.br (.gpr 16#5)) s7 = wState s0 c I Tb fn N by
    show execInstWithSvc _ _ _ = _
    rw [ex_br, x7]; rfl]
  exact Steps.refl _

theorem sat_false' {m : Memory} {F : SepProp} (h : m ⊨ ⌜False⌝ ∗ F) : False :=
  (sat_pure_sep.mp h).1

/-- `spec` with the resource `D` added to its pre- and postcondition. -/
def withRes {α : Type} (D : SepProp) (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 => spec.pre x s0 ∗ D
    post := fun x s0 sf => spec.post x s0 sf ∗ D }

/-- The compose rule. -/
theorem wrap_compose {α : Type} {P : Program} (spec : Spec α) (D : SepProp)
    {e c d I k fn : BitVec 64} {N : BitVec 5} (hW : WrapCode P e c d I k N)
    (hN31 : N ≠ 31#5) (hN16 : N ≠ 16#5) (hN19 : N.toNat < 19)
    (hread : ∀ x s0 R m, (m ⊨ (spec.pre x s0 ∗ D) ∗ R) →
      ∃ Tb, m.read64 I = Tb ∧ m.canRead I 8 = true ∧ m.read64 (Tb + k) = fn ∧
        m.canRead (Tb + k) 8 = true)
    (hinv : ∀ x (s s' : State), s'.sp = s.sp →
      (∀ i : BitVec 5, i ≠ 16#5 → i ≠ N → s'.readReg64 (.gpr i) = s.readReg64 (.gpr i)) →
      spec.pre x s' = spec.pre x s ∧ ∀ sf, spec.post x s' sf = spec.post x s sf)
    (hpan : ∀ x s s', spec.onPanic x s s' = ⌜False⌝)
    (hexit : ∀ x c s s', spec.onExit x c s s' = ⌜False⌝)
    (hoom : ∀ x s s', spec.onOom x s s' = ⌜False⌝)
    (hok : subroutine_ok P fn spec) :
    subroutine_ok P e (withRes D spec) := by
  intro x R s0 hpc hrun hpre hal hCL
  have hpre' : s0.mem ⊨ (spec.pre x s0 ∗ D) ∗ R := hpre
  obtain ⟨Tb, hrI, hcI, hrT, hcT⟩ := hread x s0 R s0.mem hpre'
  have hst := wrap_steps hW hN31 hpc hrun hCL hrI hcI hrT hcT
  set s4 := wState s0 c I Tb fn N with hs4
  have hregs : ∀ i : BitVec 5, i ≠ 16#5 → i ≠ N → s4.readReg64 (.gpr i) = s0.readReg64 (.gpr i) :=
    fun i h16 hN => wState_reg s0 c I Tb fn N i h16 hN
  obtain ⟨hI1, hI2⟩ := hinv x s0 s4 (wState_sp _ _ _ _ _ _) hregs
  have hm4 : s4.mem = s0.mem := wState_mem _ _ _ _ _ _
  have hpre4 : s4.mem ⊨ spec.pre x s4 ∗ (D ∗ R) := by
    rw [hm4, hI1, ← sepConj_assoc]; exact hpre'
  have hal4 : s4.spAligned = true := by
    simp only [State.spAligned] at hal ⊢; rw [wState_sp]; exact hal
  obtain ⟨sf, hst2, hout⟩ := hok x (D ∗ R) s4 (wState_pc _ _ _ _ _ _)
    (by rw [wState_status]; exact hrun) hpre4 hal4 (by rw [hm4]; exact hCL)
  refine ⟨sf, Steps.trans' hst hst2, ?_⟩
  have hne : ∀ k : Nat, 19 ≤ k → k < 31 → BitVec.ofNat 5 k ≠ 16#5 ∧ BitVec.ofNat 5 k ≠ N := by
    intro k hk1 hk2
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp at this; omega
    · intro h; have := congrArg BitVec.toNat h; simp at this; omega
  rcases hout with ⟨⟨hpcf, hspf, hrunf⟩, ⟨hspc, hcs⟩, hpost⟩ | ⟨_, hp⟩ | ⟨c, _, hp⟩ | ⟨_, hp⟩
  · left
    have hlr : s4.readReg64 Reg.lr = s0.readReg64 Reg.lr :=
      hregs 30#5 (by decide) (hne 30 (by omega) (by omega)).2
    have hsp4 : s4.sp = s0.sp := wState_sp _ _ _ _ _ _
    refine ⟨⟨by rw [hpcf, hlr], by rw [hspf, hsp4], hrunf⟩, ⟨by rw [hspc, hsp4], ?_⟩, ?_⟩
    · obtain ⟨a19, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, av⟩ := hcs
      have r : ∀ k : Nat, 19 ≤ k → k < 31 →
          s4.readReg64 (.gpr (BitVec.ofNat 5 k)) = s0.readReg64 (.gpr (BitVec.ofNat 5 k)) :=
        fun k h1 h2 => hregs _ (hne k h1 h2).1 (hne k h1 h2).2
      refine ⟨a19.trans (r 19 (by omega) (by omega)), a20.trans (r 20 (by omega) (by omega)),
        a21.trans (r 21 (by omega) (by omega)), a22.trans (r 22 (by omega) (by omega)),
        a23.trans (r 23 (by omega) (by omega)), a24.trans (r 24 (by omega) (by omega)),
        a25.trans (r 25 (by omega) (by omega)), a26.trans (r 26 (by omega) (by omega)),
        a27.trans (r 27 (by omega) (by omega)), a28.trans (r 28 (by omega) (by omega)),
        a29.trans (r 29 (by omega) (by omega)), ?_⟩
      rw [av]; show VRegFile.calleeSaved s4.vregs = VRegFile.calleeSaved s0.vregs
      rw [wState_vregs]
    · show sf.mem ⊨ (spec.post x s0 sf ∗ D) ∗ R
      rw [sepConj_assoc, ← hI2 sf]; exact hpost
  · rw [hpan] at hp; exact (sat_false' hp).elim
  · rw [hexit] at hp; exact (sat_false' hp).elim
  · rw [hoom] at hp; exact (sat_false' hp).elim

end Poly1305Debian.PG

end
end

section
section
/-! # The library's data under `dataInit`: the pointer `implementation` and the donna table -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.PG

open Arm64 Arm64.Obj

/-- The pointer `implementation`. -/
abbrev symI : String := "implementation [libsodium_la_onetimeauth_poly1305]"
/-- The donna table `crypto_onetimeauth_poly1305_donna_implementation`. -/
abbrev symT : String := "crypto_onetimeauth_poly1305_donna_implementation"
/-- The string `crypto_onetimeauth_primitive` returns. -/
abbrev symS : String := "libsodium_la_crypto_onetimeauth:.rodata.str1.8+0x0"

/-- The address of block symbol at offset `o`. -/
abbrev at_ (pl : Placement) (o : Nat) : BitVec 64 := pl.base + BitVec.ofNat 64 o

theorem bytesLE8 (v : BitVec 64) : bytesLE 8 v = unpack64 v := by
  simp [bytesLE, unpack64, List.range, List.range.loop]

abbrev LIB : PlacedLib := libsodiumDebianOnetimeauthLib

theorem resolve_out (pl : Placement) (x : String) (h : lookup x LIB.text.symbols = none) :
    LIB.text.resolve pl x = pl.ρ x := by
  simp [CodeBlock.resolve, h]

theorem resolve_in (pl : Placement) (x : String) (o : Nat) (h : lookup x LIB.text.symbols = some o) :
    LIB.text.resolve pl x = at_ pl o := by
  simp [CodeBlock.resolve, h]

/-- The pointer's data object. -/
abbrev dI : SymDataInfo :=
  { sym := symI, align := 8, readOnly := false, zeroTail := 0,
    bytes := libsodiumDebianOnetimeauthPlacedData1,
    relocs := [{ off := 0, kind := .abs64, sym := symT }] }

/-- The table's data object. -/
abbrev dT : SymDataInfo :=
  { sym := symT, align := 8, readOnly := false, zeroTail := 0,
    bytes := libsodiumDebianOnetimeauthPlacedData2,
    relocs := [
      { off := 0, kind := .abs64, sym := "crypto_onetimeauth_poly1305_donna [libsodium_la_poly1305_donna]" },
      { off := 8, kind := .abs64, sym := "crypto_onetimeauth_poly1305_donna_verify [libsodium_la_poly1305_donna]" },
      { off := 16, kind := .abs64, sym := "crypto_onetimeauth_poly1305_donna_init [libsodium_la_poly1305_donna]" },
      { off := 24, kind := .abs64, sym := "crypto_onetimeauth_poly1305_donna_update [libsodium_la_poly1305_donna]" },
      { off := 32, kind := .abs64, sym := "crypto_onetimeauth_poly1305_donna_final [libsodium_la_poly1305_donna]" }] }

/-- The string's data object. -/
abbrev dS : SymDataInfo :=
  { sym := symS, align := 8, readOnly := true, zeroTail := 0,
    bytes := libsodiumDebianOnetimeauthPlacedData0, relocs := [] }

theorem data_eq : libsodiumDebianOnetimeauthData = [dS, dI, dT] := rfl

theorem dataInit_eq (pl : Placement) :
    LIB.dataInit pl =
      ((pl.ρ symS ↦ᵣ LIB.patchedData pl dS) ∗
        ((pl.ρ symI ↦ₛ LIB.patchedData pl dI) ∗ (pl.ρ symT ↦ₛ LIB.patchedData pl dT))) := by
  simp only [PlacedLib.dataInit, LIB, libsodiumDebianOnetimeauthLib, data_eq, List.map, sepAll]
  rfl

theorem pdI (pl : Placement) : LIB.patchedData pl dI = unpack64 (pl.ρ symT) := by
  simp only [PlacedLib.patchedData, PlacedLib.patchDataReloc, List.foldl,
    resolve_out pl symT (by decide)]
  simp [libsodiumDebianOnetimeauthPlacedData1, addSignedAddr, bytesLE8]

theorem pdT (pl : Placement) : LIB.patchedData pl dT =
    unpack64 (at_ pl 0x584) ++ unpack64 (at_ pl 0x640) ++ unpack64 (at_ pl 0x3ac) ++
      unpack64 (at_ pl 0x400) ++ unpack64 (at_ pl 0x564) := by
  simp only [PlacedLib.patchedData, PlacedLib.patchDataReloc, List.foldl,
    resolve_in pl "crypto_onetimeauth_poly1305_donna [libsodium_la_poly1305_donna]" 0x584 (by decide),
    resolve_in pl "crypto_onetimeauth_poly1305_donna_verify [libsodium_la_poly1305_donna]" 0x640 (by decide),
    resolve_in pl "crypto_onetimeauth_poly1305_donna_init [libsodium_la_poly1305_donna]" 0x3ac (by decide),
    resolve_in pl "crypto_onetimeauth_poly1305_donna_update [libsodium_la_poly1305_donna]" 0x400 (by decide),
    resolve_in pl "crypto_onetimeauth_poly1305_donna_final [libsodium_la_poly1305_donna]" 0x564 (by decide)]
  simp [libsodiumDebianOnetimeauthPlacedData2, addSignedAddr, bytesLE8, unpack64]

end Poly1305Debian.PG

end
end

section
section
/-! # The public functions meet the donna functions' contracts with the data lent -/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Poly1305Debian.PG

open Arm64 Arm64.Obj
open Poly1305Libsodium (StateRep bytesIn)

/-! ## Reading the pointer and the table -/

theorem read_mid {m : Memory} {a v : BitVec 64} {F : SepProp} (A B : List (BitVec 8))
    (hs : m ⊨ (a ↦ₛ (A ++ unpack64 v ++ B)) ∗ F) :
    m.read64 (a + BitVec.ofNat 64 A.length) = v ∧
      m.canRead (a + BitVec.ofNat 64 A.length) 8 = true := by
  rw [List.append_assoc, pointsToBytes_append, pointsToBytes_append, ← pointsTo64_eq_bytes] at hs
  have hs' : m ⊨ ((a + BitVec.ofNat 64 A.length) ↦₆₄ v) ∗
      ((a ↦ₛ A) ∗ ((a + BitVec.ofNat 64 A.length + BitVec.ofNat 64 (unpack64 v).length) ↦ₛ B) ∗ F) :=
    Satisfies.of_eq hs
  exact ⟨(sat64_read hs').1, (sat64_read hs').2.1⟩

/-- The table entry `j` (byte offset `8 j`) holds the donna function at text offset `o`. -/
theorem data_reads (pl : Placement) {m : Memory} {X R : SepProp}
    (hs : m ⊨ (X ∗ LIB.dataInit pl) ∗ R) :
    (m.read64 (pl.ρ symI) = pl.ρ symT ∧ m.canRead (pl.ρ symI) 8 = true) ∧
    (m.read64 (pl.ρ symT + 0#64) = at_ pl 0x584 ∧ m.canRead (pl.ρ symT + 0#64) 8 = true) ∧
    (m.read64 (pl.ρ symT + 16#64) = at_ pl 0x3ac ∧ m.canRead (pl.ρ symT + 16#64) 8 = true) ∧
    (m.read64 (pl.ρ symT + 24#64) = at_ pl 0x400 ∧ m.canRead (pl.ρ symT + 24#64) 8 = true) ∧
    (m.read64 (pl.ρ symT + 32#64) = at_ pl 0x564 ∧ m.canRead (pl.ρ symT + 32#64) 8 = true) := by
  rw [dataInit_eq, pdI, pdT] at hs
  have hI : m ⊨ (pl.ρ symI ↦ₛ ([] ++ unpack64 (pl.ρ symT) ++ [])) ∗
      ((pl.ρ symS ↦ᵣ LIB.patchedData pl dS) ∗ (pl.ρ symT ↦ₛ (unpack64 (at_ pl 0x584) ++
        unpack64 (at_ pl 0x640) ++ unpack64 (at_ pl 0x3ac) ++ unpack64 (at_ pl 0x400) ++
        unpack64 (at_ pl 0x564))) ∗ X ∗ R) := by
    simp only [List.nil_append, List.append_nil]; exact Satisfies.of_eq hs
  have hT : ∀ (A B : List (BitVec 8)) (v : BitVec 64),
      unpack64 (at_ pl 0x584) ++ unpack64 (at_ pl 0x640) ++ unpack64 (at_ pl 0x3ac) ++
        unpack64 (at_ pl 0x400) ++ unpack64 (at_ pl 0x564) = A ++ unpack64 v ++ B →
      m.read64 (pl.ρ symT + BitVec.ofNat 64 A.length) = v ∧
        m.canRead (pl.ρ symT + BitVec.ofNat 64 A.length) 8 = true := by
    intro A B v he
    rw [he] at hs
    have h2 : m ⊨ (pl.ρ symT ↦ₛ (A ++ unpack64 v ++ B)) ∗
        ((pl.ρ symS ↦ᵣ LIB.patchedData pl dS) ∗ (pl.ρ symI ↦ₛ unpack64 (pl.ρ symT)) ∗ X ∗ R) :=
      Satisfies.of_eq hs
    exact read_mid A B h2
  have r0 := hT [] (unpack64 (at_ pl 0x640) ++ unpack64 (at_ pl 0x3ac) ++
    unpack64 (at_ pl 0x400) ++ unpack64 (at_ pl 0x564)) (at_ pl 0x584)
    (by simp only [List.nil_append, List.append_assoc])
  have r2 := hT (unpack64 (at_ pl 0x584) ++ unpack64 (at_ pl 0x640))
    (unpack64 (at_ pl 0x400) ++ unpack64 (at_ pl 0x564)) (at_ pl 0x3ac)
    (by simp only [List.append_assoc])
  have r3 := hT (unpack64 (at_ pl 0x584) ++ unpack64 (at_ pl 0x640) ++ unpack64 (at_ pl 0x3ac))
    (unpack64 (at_ pl 0x564)) (at_ pl 0x400)
    (by simp only [List.append_assoc])
  have r4 := hT (unpack64 (at_ pl 0x584) ++ unpack64 (at_ pl 0x640) ++ unpack64 (at_ pl 0x3ac) ++
    unpack64 (at_ pl 0x400)) [] (at_ pl 0x564) (by simp only [List.append_assoc, List.append_nil])
  simp only [List.length_append, unpack64_length, List.length_nil] at r0 r2 r3 r4
  have rI := read_mid [] [] hI
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at rI
  exact ⟨rI, r0, r2, r3, r4⟩

/-! ## The specs look at the entry state only through `sp` and `x0`–`x3` -/

theorem inv_init (Rep : StateRep) : ∀ x (s s' : State), s'.sp = s.sp →
    (∀ i : BitVec 5, i ≠ 16#5 → i ≠ 2#5 → s'.readReg64 (.gpr i) = s.readReg64 (.gpr i)) →
    (initSpec Rep).pre x s' = (initSpec Rep).pre x s ∧
      ∀ sf, (initSpec Rep).post x s' sf = (initSpec Rep).post x s sf := by
  intro x s s' _ hr
  obtain ⟨ro, st, key⟩ := x
  have h0 : s'.readReg64 Reg.x0 = s.readReg64 Reg.x0 := hr 0#5 (by decide) (by decide)
  have h1 : s'.readReg64 Reg.x1 = s.readReg64 Reg.x1 := hr 1#5 (by decide) (by decide)
  simp only [initSpec, h0, h1]
  exact ⟨trivial, fun _ => trivial⟩

theorem inv_update (Rep : StateRep) : ∀ x (s s' : State), s'.sp = s.sp →
    (∀ i : BitVec 5, i ≠ 16#5 → i ≠ 3#5 → s'.readReg64 (.gpr i) = s.readReg64 (.gpr i)) →
    (updateSpec Rep).pre x s' = (updateSpec Rep).pre x s ∧
      ∀ sf, (updateSpec Rep).post x s' sf = (updateSpec Rep).post x s sf := by
  intro x s s' hsp hr
  obtain ⟨ro, st, key, m, inp⟩ := x
  have h0 : s'.readReg64 Reg.x0 = s.readReg64 Reg.x0 := hr 0#5 (by decide) (by decide)
  have h1 : s'.readReg64 Reg.x1 = s.readReg64 Reg.x1 := hr 1#5 (by decide) (by decide)
  have h2 : s'.readReg64 Reg.x2 = s.readReg64 Reg.x2 := hr 2#5 (by decide) (by decide)
  simp only [updateSpec, stackFrame, h0, h1, h2, hsp]
  exact ⟨trivial, fun _ => trivial⟩

theorem inv_final (Rep : StateRep) : ∀ x (s s' : State), s'.sp = s.sp →
    (∀ i : BitVec 5, i ≠ 16#5 → i ≠ 2#5 → s'.readReg64 (.gpr i) = s.readReg64 (.gpr i)) →
    (finalSpec Rep).pre x s' = (finalSpec Rep).pre x s ∧
      ∀ sf, (finalSpec Rep).post x s' sf = (finalSpec Rep).post x s sf := by
  intro x s s' hsp hr
  obtain ⟨st, key, m, mac⟩ := x
  have h0 : s'.readReg64 Reg.x0 = s.readReg64 Reg.x0 := hr 0#5 (by decide) (by decide)
  have h1 : s'.readReg64 Reg.x1 = s.readReg64 Reg.x1 := hr 1#5 (by decide) (by decide)
  simp only [finalSpec, stackFrame, h0, h1, hsp]
  exact ⟨trivial, fun _ => trivial⟩

theorem inv_oneshot (pl : Placement) : ∀ x (s s' : State), s'.sp = s.sp →
    (∀ i : BitVec 5, i ≠ 16#5 → i ≠ 4#5 → s'.readReg64 (.gpr i) = s.readReg64 (.gpr i)) →
    (oneshotSpec pl).pre x s' = (oneshotSpec pl).pre x s ∧
      ∀ sf, (oneshotSpec pl).post x s' sf = (oneshotSpec pl).post x s sf := by
  intro x s s' hsp hr
  obtain ⟨roM, roK, out, m, key, gd⟩ := x
  have h0 : s'.readReg64 Reg.x0 = s.readReg64 Reg.x0 := hr 0#5 (by decide) (by decide)
  have h1 : s'.readReg64 Reg.x1 = s.readReg64 Reg.x1 := hr 1#5 (by decide) (by decide)
  have h2 : s'.readReg64 Reg.x2 = s.readReg64 Reg.x2 := hr 2#5 (by decide) (by decide)
  have h3 : s'.readReg64 Reg.x3 = s.readReg64 Reg.x3 := hr 3#5 (by decide) (by decide)
  simp only [oneshotSpec, stackFrame, h0, h1, h2, h3, hsp]
  exact ⟨trivial, fun _ => trivial⟩

/-! ## The code of the four entry points -/

theorem at_add (pl : Placement) (o j : Nat) :
    at_ pl o + BitVec.ofNat 64 j = at_ pl (o + j) := by
  simp only [at_]; rw [BitVec.add_assoc, BitVec.ofNat_add]

section
variable {pl : Placement} {ex : String → Option (State → State)}
  (hP : libsodiumDebianOnetimeauthLib.Placeable pl)
include hP

theorem wc_init : WrapCode (P pl ex) (at_ pl 0x48) (at_ pl 0xe0) 148#64 (pl.ρ symI) 16#64 2#5 where
  b_ok := by rw [at_add pl 0x48 4, at_add pl _ 148]
  f0 := fun m hCL => by rw [fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f1 := fun m hCL => by
    rw [at_add pl 0x48 4, fetch_b hP hCL (off := 0x4c) (tgt := 0xe0)
      (r := { off := 76, kind := .jump26, sym := "crypto_onetimeauth_poly1305_init" })
      (by decide) (by decide) (by rfl) (by decide) (by decide) (by rfl) (by rfl) rfl rfl (by rfl)
      148#64 (by rfl)]
    rfl
  f2 := fun m hCL => by rw [fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f3 := fun m hCL => by
    rw [at_add pl 0xe0 4, fetch_adrp hP hCL (off := 0xe4)
      (r := { off := 228, kind := .adrpHi21, sym := symI }) (W := 0x90000002#32)
      (by decide) (by decide) (by rfl) rfl (by decide) (by decide) (by rfl) (by rfl) rfl rfl
      (by decide) (by rfl) (Or.inr (Or.inl ⟨rfl, rfl⟩))]
  f4 := fun m hCL => by
    rw [at_add pl 0xe0 8, fetch_ldr_lo12 hP hCL (off := 0xe8)
      (r := { off := 232, kind := .ldst64Lo12, sym := symI }) (A := 0xf9400042#32)
      (by decide) (by decide) (by rfl) rfl (by decide) (by decide) (by rfl) (by rfl) rfl rfl
      (by decide) (by rfl) (Or.inr (Or.inl ⟨rfl, rfl⟩))]
  f5 := fun m hCL => by rw [at_add pl 0xe0 12, fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f6 := fun m hCL => by rw [at_add pl 0xe0 16, fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f7 := fun m hCL => by rw [at_add pl 0xe0 20, fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl

theorem wc_oneshot : WrapCode (P pl ex) (at_ pl 0x2c) (at_ pl 0xa0) 112#64 (pl.ρ symI) 0#64 4#5 where
  b_ok := by rw [at_add pl 0x2c 4, at_add pl _ 112]
  f0 := fun m hCL => by rw [fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f1 := fun m hCL => by
    rw [at_add pl 0x2c 4, fetch_b hP hCL (off := 0x2c+4) (tgt := 0xa0)
      (r := { off := 48, kind := .jump26, sym := "crypto_onetimeauth_poly1305" })
      (by decide) (by decide) (by rfl) (by decide) (by decide) (by rfl) (by rfl) rfl rfl (by rfl)
      112#64 (by rfl)]
    rfl
  f2 := fun m hCL => by rw [fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f3 := fun m hCL => by
    rw [at_add pl 0xa0 4, fetch_adrp hP hCL (off := 0xa0+4)
      (r := { off := 164, kind := .adrpHi21, sym := symI }) (W := 0x90000004#32)
      (by decide) (by decide) (by rfl) rfl (by decide) (by decide) (by rfl) (by rfl) rfl rfl
      (by decide) (by rfl) (Or.inl ⟨rfl, rfl⟩)]
  f4 := fun m hCL => by
    rw [at_add pl 0xa0 8, fetch_ldr_lo12 hP hCL (off := 0xa0+8)
      (r := { off := 168, kind := .ldst64Lo12, sym := symI }) (A := 0xf9400084#32)
      (by decide) (by decide) (by rfl) rfl (by decide) (by decide) (by rfl) (by rfl) rfl rfl
      (by decide) (by rfl) (Or.inl ⟨rfl, rfl⟩)]
  f5 := fun m hCL => by rw [at_add pl 0xa0 12, fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f6 := fun m hCL => by rw [at_add pl 0xa0 16, fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f7 := fun m hCL => by rw [at_add pl 0xa0 20, fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl

theorem wc_update : WrapCode (P pl ex) (at_ pl 0x50) (at_ pl 0x100) 172#64 (pl.ρ symI) 24#64 3#5 where
  b_ok := by rw [at_add pl 0x50 4, at_add pl _ 172]
  f0 := fun m hCL => by rw [fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f1 := fun m hCL => by
    rw [at_add pl 0x50 4, fetch_b hP hCL (off := 0x50+4) (tgt := 0x100)
      (r := { off := 84, kind := .jump26, sym := "crypto_onetimeauth_poly1305_update" })
      (by decide) (by decide) (by rfl) (by decide) (by decide) (by rfl) (by rfl) rfl rfl (by rfl)
      172#64 (by rfl)]
    rfl
  f2 := fun m hCL => by rw [fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f3 := fun m hCL => by
    rw [at_add pl 0x100 4, fetch_adrp hP hCL (off := 0x100+4)
      (r := { off := 260, kind := .adrpHi21, sym := symI }) (W := 0x90000003#32)
      (by decide) (by decide) (by rfl) rfl (by decide) (by decide) (by rfl) (by rfl) rfl rfl
      (by decide) (by rfl) (Or.inr (Or.inr ⟨rfl, rfl⟩))]
  f4 := fun m hCL => by
    rw [at_add pl 0x100 8, fetch_ldr_lo12 hP hCL (off := 0x100+8)
      (r := { off := 264, kind := .ldst64Lo12, sym := symI }) (A := 0xf9400063#32)
      (by decide) (by decide) (by rfl) rfl (by decide) (by decide) (by rfl) (by rfl) rfl rfl
      (by decide) (by rfl) (Or.inr (Or.inr ⟨rfl, rfl⟩))]
  f5 := fun m hCL => by rw [at_add pl 0x100 12, fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f6 := fun m hCL => by rw [at_add pl 0x100 16, fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f7 := fun m hCL => by rw [at_add pl 0x100 20, fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl

theorem wc_final : WrapCode (P pl ex) (at_ pl 0x60) (at_ pl 0x120) 188#64 (pl.ρ symI) 32#64 2#5 where
  b_ok := by rw [at_add pl 0x60 4, at_add pl _ 188]
  f0 := fun m hCL => by rw [fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f1 := fun m hCL => by
    rw [at_add pl 0x60 4, fetch_b hP hCL (off := 0x60+4) (tgt := 0x120)
      (r := { off := 100, kind := .jump26, sym := "crypto_onetimeauth_poly1305_final" })
      (by decide) (by decide) (by rfl) (by decide) (by decide) (by rfl) (by rfl) rfl rfl (by rfl)
      188#64 (by rfl)]
    rfl
  f2 := fun m hCL => by rw [fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f3 := fun m hCL => by
    rw [at_add pl 0x120 4, fetch_adrp hP hCL (off := 0x120+4)
      (r := { off := 292, kind := .adrpHi21, sym := symI }) (W := 0x90000002#32)
      (by decide) (by decide) (by rfl) rfl (by decide) (by decide) (by rfl) (by rfl) rfl rfl
      (by decide) (by rfl) (Or.inr (Or.inl ⟨rfl, rfl⟩))]
  f4 := fun m hCL => by
    rw [at_add pl 0x120 8, fetch_ldr_lo12 hP hCL (off := 0x120+8)
      (r := { off := 296, kind := .ldst64Lo12, sym := symI }) (A := 0xf9400042#32)
      (by decide) (by decide) (by rfl) rfl (by decide) (by decide) (by rfl) (by rfl) rfl rfl
      (by decide) (by rfl) (Or.inr (Or.inl ⟨rfl, rfl⟩))]
  f5 := fun m hCL => by rw [at_add pl 0x120 12, fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f6 := fun m hCL => by rw [at_add pl 0x120 16, fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl
  f7 := fun m hCL => by rw [at_add pl 0x120 20, fetch_plain hP hCL (by decide) (by decide) (by rfl)]; rfl

end

/-! ## The goal -/

theorem reads_at (pl : Placement) (k o : BitVec 64) {spec : SepProp}
    (h : ∀ m R, (m ⊨ (spec ∗ LIB.dataInit pl) ∗ R) →
      m.read64 (pl.ρ symT + k) = o ∧ m.canRead (pl.ρ symT + k) 8 = true) :
    ∀ R m, (m ⊨ (spec ∗ LIB.dataInit pl) ∗ R) →
      ∃ Tb, m.read64 (pl.ρ symI) = Tb ∧ m.canRead (pl.ρ symI) 8 = true ∧ m.read64 (Tb + k) = o ∧
        m.canRead (Tb + k) 8 = true :=
  fun R m hs => ⟨pl.ρ symT, (data_reads pl hs).1.1, (data_reads pl hs).1.2, (h m R hs).1, (h m R hs).2⟩

theorem publicOk_init_update_final_oneshot_dev :
    (∃ Rep : Poly1305Libsodium.StateRep, initPublicOk Rep ∧ updatePublicOk Rep ∧ finalPublicOk Rep) ∧
      oneshotPublicOk := by
  obtain ⟨⟨Rep, hI, hU, hF⟩, hO⟩ := Poly1305Debian.internalOk_donna_init_update_final_oneshot
  refine ⟨⟨Rep, ⟨by decide, fun pl hP hG ex hZ hM hL => ?_⟩, ⟨by decide, fun pl hP hG ex hZ hM hL => ?_⟩,
    ⟨by decide, fun pl hP hG ex hZ hM hL => ?_⟩⟩, ⟨by decide, fun pl hP hG ex hZ hM hL => ?_⟩⟩
  · have hok := hI.2 pl hP hG ex hZ hM hL
    exact wrap_compose (P := P pl ex) (initSpec Rep) (LIB.dataInit pl) (fn := at_ pl 0x3ac)
      (wc_init hP) (by decide) (by decide) (by decide)
      (fun x s0 => reads_at pl 16#64 _ (fun _ _ hs => (data_reads pl hs).2.2.1))
      (inv_init Rep) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) hok
  · have hok := hU.2 pl hP hG ex hZ hM hL
    exact wrap_compose (P := P pl ex) (updateSpec Rep) (LIB.dataInit pl) (fn := at_ pl 0x400)
      (wc_update hP) (by decide) (by decide) (by decide)
      (fun x s0 => reads_at pl 24#64 _ (fun _ _ hs => (data_reads pl hs).2.2.2.1))
      (inv_update Rep) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) hok
  · have hok := hF.2 pl hP hG ex hZ hM hL
    exact wrap_compose (P := P pl ex) (finalSpec Rep) (LIB.dataInit pl) (fn := at_ pl 0x564)
      (wc_final hP) (by decide) (by decide) (by decide)
      (fun x s0 => reads_at pl 32#64 _ (fun _ _ hs => (data_reads pl hs).2.2.2.2))
      (inv_final Rep) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) hok
  · have hok := hO.2 pl hP hG ex hZ hM hL
    exact wrap_compose (P := P pl ex) (oneshotSpec pl) (LIB.dataInit pl) (fn := at_ pl 0x584)
      (wc_oneshot hP) (by decide) (by decide) (by decide)
      (fun x s0 => reads_at pl 0#64 _ (fun _ _ hs => (data_reads pl hs).2.1))
      (inv_oneshot pl) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) hok

end Poly1305Debian.PG

end
end

section
open Poly1305Debian

theorem solution :
    (∃ Rep : Poly1305Libsodium.StateRep, initPublicOk Rep ∧ updatePublicOk Rep ∧ finalPublicOk Rep) ∧
      oneshotPublicOk := by
  apply Poly1305Debian.PG.publicOk_init_update_final_oneshot_dev <;> assumption

end
