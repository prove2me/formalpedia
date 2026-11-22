-- Prove2me | solution 1 for ZlibCrc32.subroutineOk_crc32_combine_and_crc32_combine64
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T11:34:06.842797+00:00
-- url     : https://prove2.me/submissions/09eef235-82b6-4711-9730-429e823d8936

import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Definitions.Def_ZlibCrc32_Spec
import Theorems.Thm_ZlibCrc32_crc_tables_eq
import Theorems.Thm_KadatchJenkins_crc_append_of_crcs
import Mathlib.RingTheory.PrincipalIdealDomain

section
/-! # Reflected CRC-32 arithmetic: `x · b mod P`, `multmodp`, powers of `x` -/

open Polynomial KadatchJenkins

namespace ZlibCrc32.Small

theorem coeff_regPoly {D : ℕ} (r : BitVec D) (n : ℕ) :
    (regPoly r).coeff n = if n < D ∧ r.getLsbD (D - 1 - n) = true then 1 else 0 := by
  unfold regPoly
  rw [finsetSum_coeff]
  simp only [apply_ite (fun p : (ZMod 2)[X] => p.coeff n), coeff_X_pow, coeff_zero]
  split_ifs with h
  · obtain ⟨hn, hb⟩ := h
    rw [Finset.sum_eq_single (⟨D - 1 - n, by omega⟩ : Fin D)]
    · simp only [hb, if_true]; rw [if_pos]; omega
    · intro i _ hi
      split_ifs with h1 h2
      · exfalso; apply hi; ext; simp only; omega
      · rfl
      · rfl
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    split_ifs with h1 h2
    · exfalso; apply h; refine ⟨by omega, ?_⟩; rw [show D - 1 - n = (i : ℕ) by omega]; exact h1
    · rfl
    · rfl

theorem degree_regPoly_lt {D : ℕ} (r : BitVec D) : (regPoly r).degree < D := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_regPoly, if_neg]
  omega

theorem regPoly_xor {D : ℕ} (a b : BitVec D) : regPoly (a ^^^ b) = regPoly a + regPoly b := by
  ext n
  simp only [coeff_add, coeff_regPoly, BitVec.getLsbD_xor]
  by_cases hn : n < D
  · cases a.getLsbD (D - 1 - n) <;> cases b.getLsbD (D - 1 - n) <;> simp [hn] <;> decide
  · simp [hn]

theorem regPoly_zero {D : ℕ} : regPoly (0#D) = 0 := by
  unfold regPoly; simp

theorem two_eq_zero : (2 : (ZMod 2)[X]) = 0 := by
  rw [← map_ofNat C 2, show (OfNat.ofNat 2 : ZMod 2) = 0 from rfl, map_zero]

theorem crc32P_natDegree : crc32P.natDegree = 32 := by
  unfold crc32P; compute_degree!

theorem crc32P_monic : crc32P.Monic := by
  unfold crc32P; monicity!

theorem crc32P_ne_zero : crc32P ≠ 0 := crc32P_monic.ne_zero

theorem crc32P_degree : crc32P.degree = 32 := by
  rw [Polynomial.degree_eq_natDegree crc32P_ne_zero, crc32P_natDegree]; rfl

theorem regPoly_mod {D : ℕ} (r : BitVec D) (hD : D ≤ 32) : regPoly r % crc32P = regPoly r := by
  rw [Polynomial.mod_eq_self_iff crc32P_ne_zero, crc32P_degree]
  exact lt_of_lt_of_le (degree_regPoly_lt r) (by exact_mod_cast hD)

theorem mul_P_mod (y : (ZMod 2)[X]) : y * crc32P % crc32P = 0 :=
  EuclideanDomain.mod_eq_zero.2 (dvd_mul_left _ _)

theorem add_mul_P_mod (x y : (ZMod 2)[X]) : (x + y * crc32P) % crc32P = x % crc32P := by
  rw [Polynomial.add_mod, mul_P_mod, add_zero]

/-- `(a % P) * c % P = a * c % P`. -/
theorem mod_mul_mod (a c : (ZMod 2)[X]) : a % crc32P * c % crc32P = a * c % crc32P := by
  conv_rhs => rw [← EuclideanDomain.mod_add_div a crc32P]
  rw [add_mul, show crc32P * (a / crc32P) * c = (a / crc32P * c) * crc32P by ring,
    add_mul_P_mod]

theorem mul_mod_mod (a c : (ZMod 2)[X]) : c * (a % crc32P) % crc32P = c * a % crc32P := by
  rw [mul_comm, mod_mul_mod, mul_comm]

theorem add_mod' (a b : (ZMod 2)[X]) : (a + b) % crc32P = a % crc32P + b % crc32P :=
  Polynomial.add_mod a b crc32P

/-- The reflected `POLY` constant `0xedb88320` is `x^32 mod P`. -/
def POLY : BitVec 32 := 0xedb88320#32

theorem regPoly_POLY : regPoly POLY + X ^ 32 = crc32P := by
  ext n
  simp only [coeff_add, coeff_regPoly, coeff_X_pow, crc32P, coeff_X, coeff_one]
  by_cases hn : n < 33
  · interval_cases n <;> simp [POLY] <;> decide
  · have h1 : ¬ n < 32 := by omega
    simp only [h1, false_and, if_false]
    repeat rw [if_neg (by omega)]
    simp

/-- One step of `multmodp`'s `b` update: `b · x mod P` in the reflected representation. -/
def mulx (b : BitVec 32) : BitVec 32 :=
  if b.getLsbD 0 then (b >>> 1) ^^^ POLY else b >>> 1

theorem regPoly_mul_X (b : BitVec 32) :
    regPoly b * X = regPoly (b >>> 1) + (if b.getLsbD 0 then X ^ 32 else 0) := by
  ext n
  rcases n with _ | m
  · simp [coeff_regPoly, coeff_mul_X_zero, apply_ite (fun p : (ZMod 2)[X] => p.coeff 0)]
  · rw [coeff_mul_X, coeff_add, coeff_regPoly, coeff_regPoly,
      apply_ite (fun p : (ZMod 2)[X] => p.coeff (m + 1)), coeff_X_pow, coeff_zero,
      BitVec.getLsbD_ushiftRight]
    by_cases hm : m < 31
    · rw [if_neg (show ¬ (m + 1 = 32) by omega)]
      rw [show 1 + (32 - 1 - (m + 1)) = 32 - 1 - m by omega]
      by_cases hb : b.getLsbD (32 - 1 - m) <;> simp [hb, show m + 1 < 32 by omega, show m < 32 by omega]
    · by_cases hm' : m = 31
      · subst hm'; cases b.getLsbD 0 <;> simp
      · have h1 : ¬ m < 32 := by omega
        have h2 : ¬ m + 1 < 32 := by omega
        simp only [h1, h2, false_and, if_false, zero_add]
        rw [if_neg (show ¬ m + 1 = 32 by omega)]
        split_ifs <;> rfl

theorem regPoly_mulx_eq (b : BitVec 32) :
    regPoly (mulx b) = regPoly b * X + (if b.getLsbD 0 then crc32P else 0) := by
  rw [regPoly_mul_X]
  unfold mulx
  cases hb : b.getLsbD 0
  · simp
  · simp only [if_true, regPoly_xor, ← regPoly_POLY]
    linear_combination (-(X : (ZMod 2)[X]) ^ 32) * two_eq_zero

theorem regPoly_mulx (b : BitVec 32) : regPoly (mulx b) = regPoly b * X % crc32P := by
  rw [← regPoly_mod (mulx b) le_rfl, regPoly_mulx_eq]
  split_ifs
  · have := add_mul_P_mod (regPoly b * X) 1; rw [one_mul] at this; exact this
  · rw [add_zero]

/-- `b · x^k mod P`. -/
def mulxN (k : ℕ) (b : BitVec 32) : BitVec 32 := mulx^[k] b

theorem mulxN_succ (k : ℕ) (b : BitVec 32) : mulxN (k + 1) b = mulx (mulxN k b) :=
  Function.iterate_succ_apply' mulx k b

theorem regPoly_mulxN (k : ℕ) (b : BitVec 32) :
    regPoly (mulxN k b) = regPoly b * X ^ k % crc32P := by
  induction k with
  | zero => simp [mulxN, regPoly_mod]
  | succ k ih => rw [mulxN_succ, regPoly_mulx, ih, mod_mul_mod, pow_succ, mul_assoc]

/-- The accumulator of `multmodp(a, b)` after the bits for `x^0, …, x^(j-1)` of `a`. -/
def pAcc (a b : BitVec 32) (j : ℕ) : BitVec 32 :=
  (List.range j).foldl (fun p k => if a.getLsbD (31 - k) then p ^^^ mulxN k b else p) 0#32

theorem pAcc_succ (a b : BitVec 32) (j : ℕ) :
    pAcc a b (j + 1) = if a.getLsbD (31 - j) then pAcc a b j ^^^ mulxN j b else pAcc a b j := by
  simp [pAcc, List.range_succ, List.foldl_append]

/-- The low part `∑_{k<j} a_{x^k} x^k` of the polynomial of `a`. -/
noncomputable def aPoly (a : BitVec 32) (j : ℕ) : (ZMod 2)[X] :=
  ∑ k ∈ Finset.range j, if a.getLsbD (31 - k) then X ^ k else 0

theorem regPoly_pAcc (a b : BitVec 32) (j : ℕ) :
    regPoly (pAcc a b j) = aPoly a j * regPoly b % crc32P := by
  induction j with
  | zero => simp [pAcc, aPoly, regPoly_zero]
  | succ j ih =>
    rw [pAcc_succ, aPoly, Finset.sum_range_succ, ← aPoly, add_mul, add_mod']
    split_ifs
    · rw [regPoly_xor, ih, regPoly_mulxN, mul_comm (X ^ j)]
    · rw [ih, zero_mul, EuclideanDomain.zero_mod, add_zero]

theorem aPoly_32 (a : BitVec 32) : aPoly a 32 = regPoly a := by
  ext n
  rw [coeff_regPoly, aPoly, finsetSum_coeff]
  simp only [apply_ite (fun p : (ZMod 2)[X] => p.coeff n), coeff_X_pow, coeff_zero]
  by_cases hn : n < 32
  · rw [Finset.sum_eq_single n]
    · simp [hn]
    · intro k _ hk; split_ifs <;> first | rfl | omega
    · intro h; simp at h; omega
  · rw [Finset.sum_eq_zero]
    · simp [hn]
    · intro k hk; simp at hk; split_ifs <;> first | rfl | omega

/-- The result of `multmodp(a, b)`: `a · b mod P`. -/
theorem regPoly_pAcc_32 (a b : BitVec 32) :
    regPoly (pAcc a b 32) = regPoly a * regPoly b % crc32P := by
  rw [regPoly_pAcc, aPoly_32]

/-- Once the remaining bits of `a` are clear, the accumulator is final. -/
theorem pAcc_eq_32 (a b : BitVec 32) (j : ℕ) (hj : j ≤ 32)
    (h : ∀ k, j ≤ k → k < 32 → a.getLsbD (31 - k) = false) : pAcc a b j = pAcc a b 32 := by
  suffices H : ∀ d, j + d ≤ 32 → pAcc a b j = pAcc a b (j + d) by
    have := H (32 - j) (by omega); rwa [show j + (32 - j) = 32 by omega] at this
  intro d
  induction d with
  | zero => intro; rfl
  | succ d ih =>
    intro hd
    rw [ih (by omega), ← add_assoc, pAcc_succ, if_neg (by rw [h (j + d) (by omega) (by omega)]; simp)]

end ZlibCrc32.Small
end

section
/-! # Instruction fetch, abstract states and single-step lemmas for `zlibCrc32Lib`

Adapted from the byte-table pilot proof (`ZlibCrc32Bytewise`): the abstract state replaces the
whole general-purpose register file by a function `r`, so that one step lemma covers an
instruction shape at every register. -/

namespace ZlibCrc32.Small

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-- The placed program the statements talk about. -/
def prog (pl : Placement) : Program := zlibCrc32Lib.program pl (fun _ => none) (fun _ => none)

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

/-- Fetch at an unrelocated word: the decoded word of the object. -/
theorem fetch_plain {pl : Placement} {m : Memory} (hP : zlibCrc32Lib.Placeable pl)
    (hCL : (prog pl).CodeLoaded m) {off : Nat} {i : Instr} (hal : off % 4 = 0)
    (hlen : off + 4 ≤ 2824) (hr : zlibCrc32Text.relocAt? off = none)
    (hd : decode (zlibCrc32Text.wordAt off) = some i) :
    (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 off) = some i := by
  rw [fetch_word hP hCL hal hlen, patchedWord_plain pl hr, hd]

/-! ## Abstract states -/

/-- The entry state `s0` with the register file `r`, `pc` and flags replaced. -/
def mkS (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (ps : PState) : State :=
  { s0 with regs := ⟨r⟩, pc := pc, pstate := ps }

section lemmas
variable (s0 : State) (pc : BitVec 64) (r : BitVec 5 → BitVec 64) (ps : PState)

@[simp] theorem mkS_mem : (mkS s0 pc r ps).mem = s0.mem := rfl
@[simp] theorem mkS_pc : (mkS s0 pc r ps).pc = pc := rfl
@[simp] theorem mkS_sp : (mkS s0 pc r ps).sp = s0.sp := rfl
@[simp] theorem mkS_status : (mkS s0 pc r ps).status = s0.status := rfl
@[simp] theorem mkS_pstate : (mkS s0 pc r ps).pstate = ps := rfl
@[simp] theorem mkS_vregs : (mkS s0 pc r ps).vregs = s0.vregs := rfl

theorem rd_gpr (i : BitVec 5) :
    (mkS s0 pc r ps).readReg64 (.gpr i) = if i = 31#5 then 0#64 else r i := by
  simp [State.readReg64, RegFile.read, mkS]

@[simp] theorem rd_xzr : (mkS s0 pc r ps).readReg64 .xzr = 0#64 := rfl

theorem wr_gpr (i : BitVec 5) (v : BitVec 64) (hi : i ≠ 31#5) :
    (mkS s0 pc r ps).writeReg64 (.gpr i) v = mkS s0 pc (Function.update r i v) ps := by
  simp only [mkS, State.writeReg64, RegFile.write, beq_iff_eq, hi, if_false]
  congr 2; funext k; simp [Function.update_apply]

@[simp] theorem wr_xzr (v : BitVec 64) : (mkS s0 pc r ps).writeReg64 .xzr v = mkS s0 pc r ps := rfl
@[simp] theorem mkS_advancePC : (mkS s0 pc r ps).advancePC = mkS s0 (pc + 4#64) r ps := rfl
@[simp] theorem mkS_setPC (q : BitVec 64) : (mkS s0 pc r ps).setPC q = mkS s0 q r ps := rfl
@[simp] theorem mkS_setPState (q : PState) : (mkS s0 pc r ps).setPState q = mkS s0 pc r q := rfl

end lemmas

theorem mkS_self (s0 : State) : mkS s0 s0.pc s0.regs.regs s0.pstate = s0 := rfl

/-! ## Steps utilities -/

theorem Steps.trans' {p : Program} {a b c : State} (h1 : Steps p a b) (h2 : Steps p b c) :
    Steps p a c := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact Steps.step h (ih h2)

theorem step_mkS {pl : Placement} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {ps : PState} {inst : Instr} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem s0.mem pc = some inst) :
    Step (prog pl) (mkS s0 pc r ps) (execInstWithSvc (evalSvc Syscall.standard) inst (mkS s0 pc r ps)) := by
  have := Step.exec (prog := prog pl) (s := mkS s0 pc r ps) hrun hf
  rw [Program.evalInst] at this
  rwa [show (prog pl).svc = Syscall.standard from rfl] at this

/-! ## The 32-bit view of a register -/

/-- The low 32 bits. -/
abbrev lo (x : BitVec 64) : BitVec 32 := x.setWidth 32
/-- Zero extension of a 32-bit value. -/
abbrev W (v : BitVec 32) : BitVec 64 := v.setWidth 64

@[simp] theorem lo_W (v : BitVec 32) : lo (W v) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

/-! ## Execution of each instruction shape on an abstract state -/

section exec
variable {svc : State → State} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64} {ps : PState}

/-- `MOVZ Wd, #imm, LSL #hw`. -/
theorem ex_movz {d : BitVec 5} {imm : BitVec 16} {hw : Nat} (hd : d ≠ 31#5) :
    execInstWithSvc svc (.moveWide .W32 .MOVZ (.gpr d) imm hw) (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) (Function.update r d (W (((imm.setWidth 64) <<< hw).setWidth 32))) ps := by
  show (State.writeReg _ _ _ _).advancePC = _
  simp only [State.writeReg, wr_gpr _ _ _ _ _ _ hd, mkS_advancePC]

/-- `MOVK Wd, #imm, LSL #hw`. -/
theorem ex_movk {d : BitVec 5} {imm : BitVec 16} {hw : Nat} (hd : d ≠ 31#5) :
    execInstWithSvc svc (.moveWide .W32 .MOVK (.gpr d) imm hw) (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) (Function.update r d
        (W ((((W (lo (r d))) &&& ~~~(0xffff#64 <<< hw)) ||| ((imm.setWidth 64) <<< hw)).setWidth 32)))
        ps := by
  show (State.writeReg _ _ _ _).advancePC = _
  simp only [State.writeReg, State.readReg, State.readReg32, rd_gpr, hd, if_false,
    wr_gpr _ _ _ _ _ _ hd, mkS_advancePC]

/-- `MOV Wd, Wn` (`ORR Wd, WZR, Wn`). -/
theorem ex_movw {d n : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.logicalShift .W32 .ORR (.gpr d) .xzr (.gpr n) .LSL 0) (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) (Function.update r d (W (lo (r n)))) ps := by
  show (State.writeReg _ _ _ _).advancePC = _
  simp only [State.writeReg, State.readReg, State.readReg32, rd_gpr, hn, if_false,
    wr_gpr _ _ _ _ _ _ hd, mkS_advancePC, evalLogical, shiftVal, shift32, rd_xzr]
  congr 3
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

/-- `MOV Wd, WZR`. -/
theorem ex_movw0 {d : BitVec 5} (hd : d ≠ 31#5) :
    execInstWithSvc svc (.logicalShift .W32 .ORR (.gpr d) .xzr .xzr .LSL 0) (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) (Function.update r d 0#64) ps := by
  show (State.writeReg _ _ _ _).advancePC = _
  simp only [State.writeReg, State.readReg, State.readReg32, wr_gpr _ _ _ _ _ _ hd, mkS_advancePC,
    evalLogical, shiftVal, shift32, rd_xzr]
  rfl

/-- `MOV Xd, Xn` (`ORR Xd, XZR, Xn`). -/
theorem ex_movx {d n : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.logicalShift .W64 .ORR (.gpr d) .xzr (.gpr n) .LSL 0) (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) (Function.update r d (r n)) ps := by
  show (State.writeReg _ _ _ _).advancePC = _
  simp only [State.writeReg, State.readReg, rd_gpr, hn, if_false,
    wr_gpr _ _ _ _ _ _ hd, mkS_advancePC, evalLogical, shiftVal, shift64, rd_xzr]
  simp

theorem eval_lsr1 (d x : BitVec 64) :
    evalBitfield .W32 .UBFM d x 1 31 = W (lo x >>> 1) := by
  simp only [evalBitfield, show (BitfieldOp.UBFM == BitfieldOp.UBFM) = true from rfl]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]
  omega

/-- `LSR Wd, Wn, #1` (`UBFM Wd, Wn, #1, #31`). -/
theorem ex_lsr1 {d n : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.bitfield .W32 .UBFM (.gpr d) (.gpr n) 1 31) (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) (Function.update r d (W (lo (r n) >>> 1))) ps := by
  show (State.writeReg _ _ _ _).advancePC = _
  simp only [State.writeReg, State.readReg, eval_lsr1, wr_gpr _ _ _ _ _ _ hd, mkS_advancePC]
  congr 3
  simp only [State.readReg32, rd_gpr, hn, if_false]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]
  omega

/-- `ASR Xd, Xn, #1` (`SBFM Xd, Xn, #1, #63`). -/
theorem ex_asr1 {d n : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.bitfield .W64 .SBFM (.gpr d) (.gpr n) 1 63) (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) (Function.update r d ((r n).sshiftRight 1)) ps := by
  show (State.writeReg _ _ _ _).advancePC = _
  simp only [State.writeReg, State.readReg, rd_gpr, hn, hd, if_false,
    wr_gpr _ _ _ _ _ _ hd, mkS_advancePC, evalBitfield]
  rfl

/-- The flags of a 32-bit `ANDS`/`TST` with result `v`. -/
def tstFlags (v : BitVec 32) : PState := { n := v.msb, z := v == 0#32, c := false, v := false }

theorem trunc_and1 (x : BitVec 64) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 x) &&& 4294967297#64) = lo x &&& 1#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp

theorem trunc_and (a b : BitVec 64) : BitVec.truncate 32
    (BitVec.zeroExtend 64 (BitVec.truncate 32 a) &&&
      BitVec.zeroExtend 64 (BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 b)) <<< (0 % 32))) =
    lo a &&& lo b := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

/-- `TST Wn, #1`. -/
theorem ex_tst1 {n : BitVec 5} (hn : n ≠ 31#5) :
    execInstWithSvc svc (.logicalImm .W32 .ANDS .xzr (.gpr n) 0x0000000100000001#64) (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) r (tstFlags (lo (r n) &&& 1#32)) := by
  show (State.setPState _ _).advancePC = _
  simp only [State.writeReg, State.readReg, State.readReg32, rd_gpr, hn, if_false, wr_xzr,
    mkS_advancePC, evalLogical, mkS_setPState, tstFlags, trunc_and1]

/-- `TST Wn, Wm`. -/
theorem ex_tst {n m : BitVec 5} (hn : n ≠ 31#5) (hm : m ≠ 31#5) :
    execInstWithSvc svc (.logicalShift .W32 .ANDS .xzr (.gpr n) (.gpr m) .LSL 0) (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) r (tstFlags (lo (r n) &&& lo (r m))) := by
  show (State.setPState _ _).advancePC = _
  simp only [State.writeReg, State.readReg, State.readReg32, rd_gpr, hn, hm, if_false, wr_xzr,
    mkS_advancePC, evalLogical, shiftVal, shift32, mkS_setPState, tstFlags, trunc_and]

/-- `EOR Wd, Wn, Wm`. -/
theorem ex_eorw {d n m : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hm : m ≠ 31#5) :
    execInstWithSvc svc (.logicalShift .W32 .EOR (.gpr d) (.gpr n) (.gpr m) .LSL 0) (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) (Function.update r d (W (lo (r n) ^^^ lo (r m)))) ps := by
  show (State.writeReg _ _ _ _).advancePC = _
  simp only [State.writeReg, State.readReg, State.readReg32, rd_gpr, hn, hm, if_false,
    wr_gpr _ _ _ _ _ _ hd, mkS_advancePC, evalLogical, shiftVal, shift32]
  congr 3
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [hi]

/-- `EOR Xd, Xn, Xm`. -/
theorem ex_eorx {d n m : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hm : m ≠ 31#5) :
    execInstWithSvc svc (.logicalShift .W64 .EOR (.gpr d) (.gpr n) (.gpr m) .LSL 0) (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) (Function.update r d (r n ^^^ r m)) ps := by
  show (State.writeReg _ _ _ _).advancePC = _
  simp only [State.writeReg, State.readReg, rd_gpr, hn, hm, if_false,
    wr_gpr _ _ _ _ _ _ hd, mkS_advancePC, evalLogical, shiftVal, shift64]
  simp

/-- `CSEL Wd, Wn, Wm, EQ`. -/
theorem ex_csel_eq {d n m : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) (hm : m ≠ 31#5) :
    execInstWithSvc svc (.condSelect .W32 .CSEL (.gpr d) (.gpr n) (.gpr m) .EQ) (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) (Function.update r d (if ps.z then W (lo (r n)) else W (lo (r m)))) ps := by
  show (State.writeReg _ _ _ _).advancePC = _
  simp only [State.writeReg, State.readReg, State.readReg32, rd_gpr, hn, hm, if_false,
    wr_gpr _ _ _ _ _ _ hd, mkS_advancePC, ConditionHolds, mkS_pstate]
  congr 3
  split <;> (apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi])

/-- `SUB Wd, Wn, #1`. -/
theorem ex_sub1 {d n : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.addSubImm .W32 .SUB (.gpr d) (.gpr n) 0x001#12 false) (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) (Function.update r d (W (lo (r n) - 1#32))) ps := by
  show (State.writeReg _ _ _ _).advancePC = _
  simp only [State.writeReg, State.readReg, State.readReg32, rd_gpr, hn, if_false,
    wr_gpr _ _ _ _ _ _ hd, mkS_advancePC, evalAddSub, AddWithCarry32]
  congr 3
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_sub]
  omega

/-- `ADD Wd, Wn, #1`. -/
theorem ex_add1 {d n : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.addSubImm .W32 .ADD (.gpr d) (.gpr n) 0x001#12 false) (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) (Function.update r d (W (lo (r n) + 1#32))) ps := by
  show (State.writeReg _ _ _ _).advancePC = _
  simp only [State.writeReg, State.readReg, State.readReg32, rd_gpr, hn, if_false,
    wr_gpr _ _ _ _ _ _ hd, mkS_advancePC, evalAddSub, AddWithCarry32]
  congr 3
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.toNat_add]
  omega

/-- `AND Wd, Wn, #0x1f`. -/
theorem ex_and31 {d n : BitVec 5} (hd : d ≠ 31#5) (hn : n ≠ 31#5) :
    execInstWithSvc svc (.logicalImm .W32 .AND (.gpr d) (.gpr n) 0x0000001f0000001f#64) (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) (Function.update r d (W (lo (r n) &&& 0x1f#32))) ps := by
  show (State.writeReg _ _ _ _).advancePC = _
  simp only [State.writeReg, State.readReg, State.readReg32, rd_gpr, hn, if_false,
    wr_gpr _ _ _ _ _ _ hd, mkS_advancePC, evalLogical]
  congr 3
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  interval_cases i <;> simp

/-- The flags of `SUBS XZR, Xn, #k` (`CMP Xn, #k`). -/
def subFlags (x y : BitVec 64) : PState := (AddWithCarry64 x (~~~y) true).2

/-- `CMP Xn, #1`. -/
theorem ex_cmp1 {n : BitVec 5} (hn : n ≠ 31#5) :
    execInstWithSvc svc (.addSubImm .W64 .SUBS .xzr (.gpr n) 0x001#12 false) (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) r (subFlags (r n) 1#64) := by
  show (State.setPState _ _).advancePC = _
  simp only [State.writeReg, State.readReg, rd_gpr, hn, if_false, wr_xzr, mkS_advancePC,
    evalAddSub, mkS_setPState, subFlags]
  rfl

theorem ex_b {off : BitVec 64} :
    execInstWithSvc svc (.b off) (mkS s0 pc r ps) = mkS s0 (pc + off) r ps := rfl

theorem ex_bcond {c : CondCode} {off : BitVec 64} :
    execInstWithSvc svc (.bCond c off) (mkS s0 pc r ps) =
      if ConditionHolds c ps then mkS s0 (pc + off) r ps else mkS s0 (pc + 4#64) r ps := rfl

theorem ex_tbz0 {n : BitVec 5} {off : BitVec 64} (hn : n ≠ 31#5) :
    execInstWithSvc svc (.tbz .W32 false (.gpr n) 0 off) (mkS s0 pc r ps) =
      if (r n).getLsbD 0 = false then mkS s0 (pc + off) r ps else mkS s0 (pc + 4#64) r ps := by
  show (if _ then _ else _) = _
  simp only [rd_gpr, hn, if_false]
  cases (r n).getLsbD 0 <;> rfl

theorem ex_cbzx {n : BitVec 5} {off : BitVec 64} (hn : n ≠ 31#5) :
    execInstWithSvc svc (.cbz .W64 false (.gpr n) off) (mkS s0 pc r ps) =
      if r n = 0#64 then mkS s0 (pc + off) r ps else mkS s0 (pc + 4#64) r ps := by
  show (if _ then _ else _) = _
  by_cases h : r n = 0#64 <;> simp [State.readReg, rd_gpr, hn, h]

theorem ex_ret :
    execInstWithSvc svc (.ret (.gpr 30#5)) (mkS s0 pc r ps) = mkS s0 (r 30#5) r ps := by
  show State.setPC _ _ = _
  simp [rd_gpr]

/-- `LDR Wd, [Xb, Wi, UXTW #2]`. -/
theorem ex_ldrw {d b i : BitVec 5} (hd : d ≠ 31#5) (hb : b ≠ 31#5) (hi : i ≠ 31#5)
    (hr : s0.mem.canRead (r b + (W (lo (r i)) <<< 2)) 4 = true) :
    execInstWithSvc svc (.ldr .W32 .W32 false (.gpr d) (.RegOffset (.gpr b) (.gpr i) .UXTW 2))
      (mkS s0 pc r ps) =
      mkS s0 (pc + 4#64) (Function.update r d (W (s0.mem.read32 (r b + (W (lo (r i)) <<< 2))))) ps := by
  rw [show execInstWithSvc svc (.ldr .W32 .W32 false (.gpr d) (.RegOffset (.gpr b) (.gpr i) .UXTW 2))
      (mkS s0 pc r ps) = execLdr .W32 .W32 false (.gpr d) (.RegOffset (.gpr b) (.gpr i) .UXTW 2)
      (mkS s0 pc r ps) from rfl]
  simp only [execLdr, checkAddrSPAligned, checkRegSPAligned, AddrMode.baseReg, evalAddrMode,
    extendVal, rd_gpr, hb, hi, if_false, mkS_mem]
  simp only [MemWidth.bytes, hr, Bool.not_true, Bool.false_eq_true, if_false, Bool.not_false]
  simp only [Memory.readSized, State.writeReg, wr_gpr _ _ _ _ _ _ hd, mkS_advancePC]
  congr 3
  apply BitVec.eq_of_getLsbD_eq; intro k hk
  simp [hk]

end exec

end ZlibCrc32.Small
end

section
/-! # Reachability of the return state, and the compiled `multmodp` loop (register-generic) -/

namespace ZlibCrc32.Small

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-! ## Bits of `m = 0x80000000 >>> j` -/

theorem getLsbD_top (n : ℕ) : (0x80000000#32 : BitVec 32).getLsbD n = decide (n = 31) := by
  rw [show (0x80000000#32 : BitVec 32) = BitVec.ofNat 32 (2 ^ 31) from rfl, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow]
  by_cases h : n = 31 <;> simp [h] <;> omega

theorem getLsbD_m (j i : ℕ) (hi : i < 32) :
    ((0x80000000#32 : BitVec 32) >>> j).getLsbD i = decide (j + i = 31) := by
  rw [BitVec.getLsbD_ushiftRight, getLsbD_top]

theorem toNat_m (j : ℕ) (hj : j < 32) : ((0x80000000#32 : BitVec 32) >>> j).toNat = 2 ^ (31 - j) := by
  rw [BitVec.toNat_ushiftRight]
  rw [show (0x80000000#32 : BitVec 32).toNat = 2 ^ 31 from rfl, Nat.shiftRight_eq_div_pow,
    show 2 ^ 31 = 2 ^ (31 - j) * 2 ^ j by rw [← pow_add]; congr 1; omega,
    Nat.mul_div_cancel _ (by positivity)]

theorem getLsbD_m1 (j i : ℕ) (hj : j < 32) :
    (((0x80000000#32 : BitVec 32) >>> j) - 1#32).getLsbD i = decide (i < 31 - j) := by
  have h1 := toNat_m j hj
  have hpos : 1 ≤ 2 ^ (31 - j) := Nat.one_le_two_pow
  have hlt : 2 ^ (31 - j) ≤ 2 ^ 31 := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (((0x80000000#32 : BitVec 32) >>> j) - 1#32).toNat = 2 ^ (31 - j) - 1 := by
    rw [BitVec.toNat_sub, h1]; simp; omega
  rw [BitVec.getLsbD, h2, Nat.testBit_two_pow_sub_one]

theorem and_eq_zero_iff (x a : BitVec 32) :
    x &&& a = 0#32 ↔ ∀ i, i < 32 → x.getLsbD i = true → a.getLsbD i = false := by
  constructor
  · intro h i hi hx
    have := congrArg (fun v => v.getLsbD i) h
    simp only [BitVec.getLsbD_and, hx, Bool.true_and, BitVec.getLsbD_zero] at this
    exact this
  · intro h
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_zero]
    cases hx : x.getLsbD i
    · simp
    · simp [h i hi hx]

theorem m_and (a : BitVec 32) (j : ℕ) (hj : j < 32) :
    ((0x80000000#32 : BitVec 32) >>> j) &&& a = 0#32 ↔ a.getLsbD (31 - j) = false := by
  rw [and_eq_zero_iff]
  constructor
  · intro h; exact h (31 - j) (by omega) (by rw [getLsbD_m _ _ (by omega)]; simp; omega)
  · intro h i hi hx
    rw [getLsbD_m _ _ hi] at hx
    simp at hx
    rw [show i = 31 - j by omega]; exact h

theorem m1_and (a : BitVec 32) (j : ℕ) (hj : j < 32) :
    (((0x80000000#32 : BitVec 32) >>> j) - 1#32) &&& a = 0#32 ↔
      ∀ k, j < k → k < 32 → a.getLsbD (31 - k) = false := by
  rw [and_eq_zero_iff]
  constructor
  · intro h k hk1 hk2; exact h (31 - k) (by omega) (by rw [getLsbD_m1 _ _ hj]; simp; omega)
  · intro h i hi hx
    rw [getLsbD_m1 _ _ hj] at hx
    simp at hx
    have := h (31 - i) (by omega) (by omega)
    rwa [show 31 - (31 - i) = i by omega] at this

theorem m_shr (j : ℕ) : ((0x80000000#32 : BitVec 32) >>> j) >>> 1 = (0x80000000#32 : BitVec 32) >>> (j + 1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_ushiftRight, getLsbD_top]
  congr 1; simp; omega

theorem getLsbD_one32 (i : ℕ) : (1#32 : BitVec 32).getLsbD i = decide (i = 0) := by
  rw [show (1#32 : BitVec 32) = BitVec.ofNat 32 (2 ^ 0) from rfl, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow]
  by_cases h : i = 0 <;> simp [h] <;> omega

theorem and1_eq_zero (b : BitVec 32) : (b &&& 1#32 = 0#32) ↔ b.getLsbD 0 = false := by
  constructor
  · intro h
    have := congrArg (fun v => v.getLsbD 0) h
    simpa [BitVec.getLsbD_and, getLsbD_one32] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, getLsbD_one32, BitVec.getLsbD_zero]
    by_cases hi0 : i = 0
    · subst hi0; simp only [decide_true, Bool.and_true, h]
    · simp [hi0]

theorem tstFlags_z (v : BitVec 32) : (tstFlags v).z = decide (v = 0#32) := by
  simp only [tstFlags]; by_cases h : v = 0#32 <;> simp [h]

/-! ## Reachability -/

/-- The callee-saved and higher registers (`x19` and up) are the entry state's. -/
def Keep (s0 : State) (r : BitVec 5 → BitVec 64) : Prop :=
  ∀ i : BitVec 5, 19 ≤ i.toNat → r i = s0.regs.regs i

theorem keep_update {s0 : State} {r : BitVec 5 → BitVec 64} (h : Keep s0 r) {d : BitVec 5}
    (hd : d.toNat < 19) (v : BitVec 64) : Keep s0 (Function.update r d v) := by
  intro i hi
  rw [Function.update_of_ne (by rintro rfl; omega)]
  exact h i hi

/-- Returned with `Φ x0` and the registers from `x19` up untouched. -/
def Fin (s0 : State) (Φ : BitVec 64 → Prop) (sf : State) : Prop :=
  ∃ r ps, sf = mkS s0 (s0.regs.regs 30#5) r ps ∧ Φ (r 0#5) ∧ Keep s0 r

def Reach (pl : Placement) (s0 : State) (Φ : BitVec 64 → Prop) (s : State) : Prop :=
  ∃ sf, Steps (prog pl) s sf ∧ Fin s0 Φ sf

theorem reach_step {pl : Placement} {s0 s s' : State} {Φ : BitVec 64 → Prop} (h : Step (prog pl) s s')
    (h' : Reach pl s0 Φ s') : Reach pl s0 Φ s := by
  obtain ⟨sf, h1, h2⟩ := h'
  exact ⟨sf, Steps.step h h1, h2⟩

theorem reach_steps {pl : Placement} {s0 s s' : State} {Φ : BitVec 64 → Prop} (h : Steps (prog pl) s s')
    (h' : Reach pl s0 Φ s') : Reach pl s0 Φ s := by
  obtain ⟨sf, h1, h2⟩ := h'
  exact ⟨sf, Steps.trans' h h1, h2⟩

theorem reach_exec {pl : Placement} {s0 : State} {Φ : BitVec 64 → Prop} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {ps : PState} {inst : Instr} {s' : State} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem s0.mem pc = some inst)
    (he : execInstWithSvc (evalSvc Syscall.standard) inst (mkS s0 pc r ps) = s')
    (h : Reach pl s0 Φ s') : Reach pl s0 Φ (mkS s0 pc r ps) := by
  rw [← he] at h
  exact reach_step (step_mkS hrun hf) h

theorem reach_ret {pl : Placement} {s0 : State} {Φ : BitVec 64 → Prop} {pc : BitVec 64}
    {r : BitVec 5 → BitVec 64} {ps : PState} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem s0.mem pc = some (.ret (.gpr 30#5))) (hk : Keep s0 r) (hΦ : Φ (r 0#5)) :
    Reach pl s0 Φ (mkS s0 pc r ps) := by
  refine reach_exec hrun hf ex_ret ⟨_, Steps.refl _, r, ps, ?_, hΦ, hk⟩
  rw [hk 30#5 (by decide)]

/-! ## The compiled `multmodp(a, b)` loop

```
L+0x00  lsr  T1, B, #1          L+0x14  tst  M, A
L+0x04  tst  B, #1              L+0x18  b.eq L
L+0x08  lsr  M, M, #1           L+0x1c  sub  T1, M, #1
L+0x0c  eor  T2, T1, Q          L+0x20  eor  P, P, B
L+0x10  csel B, T1, T2, eq      L+0x24  tst  T1, A
                                L+0x28  b.ne L
```
(`Q` holds `POLY`; exit at `L+0x2c` with `P = a·b mod p`.) -/

/-- The loop's instructions at `L`. -/
structure MMCode (pl : Placement) (m : Memory) (L : BitVec 64) (A B M P Q T1 T2 : BitVec 5) : Prop where
  f0 : (prog pl).fetchMem m L = some (.bitfield .W32 .UBFM (.gpr T1) (.gpr B) 1 31)
  f1 : (prog pl).fetchMem m (L + 4#64) = some (.logicalImm .W32 .ANDS .xzr (.gpr B) 0x0000000100000001#64)
  f2 : (prog pl).fetchMem m (L + 8#64) = some (.bitfield .W32 .UBFM (.gpr M) (.gpr M) 1 31)
  f3 : (prog pl).fetchMem m (L + 12#64) = some (.logicalShift .W32 .EOR (.gpr T2) (.gpr T1) (.gpr Q) .LSL 0)
  f4 : (prog pl).fetchMem m (L + 16#64) = some (.condSelect .W32 .CSEL (.gpr B) (.gpr T1) (.gpr T2) .EQ)
  f5 : (prog pl).fetchMem m (L + 20#64) = some (.logicalShift .W32 .ANDS .xzr (.gpr M) (.gpr A) .LSL 0)
  f6 : (prog pl).fetchMem m (L + 24#64) = some (.bCond .EQ 0xffffffffffffffe8#64)
  f7 : (prog pl).fetchMem m (L + 28#64) = some (.addSubImm .W32 .SUB (.gpr T1) (.gpr M) 0x001#12 false)
  f8 : (prog pl).fetchMem m (L + 32#64) = some (.logicalShift .W32 .EOR (.gpr P) (.gpr P) (.gpr B) .LSL 0)
  f9 : (prog pl).fetchMem m (L + 36#64) = some (.logicalShift .W32 .ANDS .xzr (.gpr T1) (.gpr A) .LSL 0)
  f10 : (prog pl).fetchMem m (L + 40#64) = some (.bCond .NE 0xffffffffffffffd8#64)

/-- The loop's registers: all general-purpose below `x19`, the written ones distinct from each
other and from `A`, `Q`. -/
def MMRegs (A B M P Q T1 T2 : BitVec 5) : Prop :=
  A.toNat < 19 ∧ B.toNat < 19 ∧ M.toNat < 19 ∧ P.toNat < 19 ∧ Q.toNat < 19 ∧ T1.toNat < 19 ∧
    T2.toNat < 19 ∧
  B ≠ M ∧ B ≠ P ∧ B ≠ T1 ∧ B ≠ T2 ∧ M ≠ P ∧ M ≠ T1 ∧ M ≠ T2 ∧ P ≠ T1 ∧ P ≠ T2 ∧ T1 ≠ T2 ∧
  A ≠ B ∧ A ≠ M ∧ A ≠ P ∧ A ≠ T1 ∧ A ≠ T2 ∧ Q ≠ B ∧ Q ≠ M ∧ Q ≠ P ∧ Q ≠ T1 ∧ Q ≠ T2

theorem ne31 {d : BitVec 5} (h : d.toNat < 19) : d ≠ 31#5 := by
  rintro rfl; simp at h

theorem mulx_csel (b : BitVec 32) :
    (if b &&& 1#32 = 0#32 then W (b >>> 1) else W ((b >>> 1) ^^^ POLY)) = W (mulx b) := by
  unfold mulx
  by_cases h : b.getLsbD 0
  · have : ¬ (b &&& 1#32 = 0#32) := by rw [and1_eq_zero]; simp [h]
    rw [if_neg this, if_pos h]
  · have : b &&& 1#32 = 0#32 := by rw [and1_eq_zero]; simpa using h
    rw [if_pos this, if_neg h]

section loop
variable {pl : Placement} {s0 : State} {Φ : BitVec 64 → Prop} {L : BitVec 64}
  {A B M P Q T1 T2 : BitVec 5}

/-- The body `L .. L+0x10`: `b := b·x mod p`, `m := m >> 1`. -/
theorem mm_body (hrun : s0.status = .Running) (hc : MMCode pl s0.mem L A B M P Q T1 T2)
    (hR : MMRegs A B M P Q T1 T2) {r : BitVec 5 → BitVec 64} {ps : PState}
    (hQ : lo (r Q) = POLY)
    (h : ∀ ps', Reach pl s0 Φ (mkS s0 (L + 20#64)
      (Function.update (Function.update (Function.update (Function.update r T1 (W (lo (r B) >>> 1)))
        M (W (lo (r M) >>> 1))) T2 (W ((lo (r B) >>> 1) ^^^ POLY))) B (W (mulx (lo (r B))))) ps')) :
    Reach pl s0 Φ (mkS s0 L r ps) := by
  obtain ⟨hA, hB, hM, hP, hQ', hT1, hT2, hBM, hBP, hBT1, hBT2, hMP, hMT1, hMT2, hPT1, hPT2, hT1T2,
    hAB, hAM, hAP, hAT1, hAT2, hQB, hQM, hQP, hQT1, hQT2⟩ := hR
  refine reach_exec hrun hc.f0 (ex_lsr1 (ne31 hT1) (ne31 hB)) ?_
  refine reach_exec hrun (by rw [show L + 4#64 = L + 4#64 from rfl]; exact hc.f1) (ex_tst1 (ne31 hB)) ?_
  rw [show L + 4#64 + 4#64 = L + 8#64 by rw [BitVec.add_assoc]; rfl]
  refine reach_exec hrun hc.f2 (ex_lsr1 (ne31 hM) (ne31 hM)) ?_
  rw [show L + 8#64 + 4#64 = L + 12#64 by rw [BitVec.add_assoc]; rfl]
  refine reach_exec hrun hc.f3 (ex_eorw (ne31 hT2) (ne31 hT1) (ne31 hQ')) ?_
  rw [show L + 12#64 + 4#64 = L + 16#64 by rw [BitVec.add_assoc]; rfl]
  refine reach_exec hrun hc.f4 (ex_csel_eq (ne31 hB) (ne31 hT1) (ne31 hT2)) ?_
  rw [show L + 16#64 + 4#64 = L + 20#64 by rw [BitVec.add_assoc]; rfl]
  simp only [Function.update_apply, hBM, hBP, hBT1, hBT2, hMP, hMT1, hMT2, hPT1, hPT2, hT1T2,
    hQB, hQM, hQP, hQT1, hQT2, hBM.symm, hBP.symm, hBT1.symm, hBT2.symm, hMP.symm, hMT1.symm,
    hMT2.symm, hPT1.symm, hPT2.symm, hT1T2.symm, hQB.symm, hQM.symm, hQP.symm, hQT1.symm,
    hQT2.symm, if_true, if_false, lo_W, hQ, tstFlags_z, decide_eq_true_eq, mulx_csel] at h ⊢
  exact h _

theorem addr_eq (L a b c : BitVec 64) (h : a + b = c) : L + a + b = L + c := by
  rw [BitVec.add_assoc, h]

/-- One iteration from the test `tst M, A` at `L+0x14` (iteration `j`, `m = 2^31 >> j`). -/
theorem mm_step (hrun : s0.status = .Running) (hc : MMCode pl s0.mem L A B M P Q T1 T2)
    (hR : MMRegs A B M P Q T1 T2) {a b : BitVec 32} {r0 : BitVec 5 → BitVec 64}
    (hk : ∀ r' ps', (∀ i, i ≠ B → i ≠ M → i ≠ P → i ≠ T1 → i ≠ T2 → r' i = r0 i) →
      r' P = W (pAcc a b 32) → Reach pl s0 Φ (mkS s0 (L + 44#64) r' ps'))
    (hA0 : lo (r0 A) = a) (hQ0 : lo (r0 Q) = POLY)
    {j : ℕ} (hj : j < 32) {r : BitVec 5 → BitVec 64} {ps : PState}
    (hex : ∃ k, j ≤ k ∧ k < 32 ∧ a.getLsbD (31 - k) = true)
    (hr : ∀ i, i ≠ B → i ≠ M → i ≠ P → i ≠ T1 → i ≠ T2 → r i = r0 i)
    (hm : lo (r M) = 0x80000000#32 >>> j) (hb : lo (r B) = mulxN j b) (hp : lo (r P) = pAcc a b j)
    (IH : j + 1 < 32 → ∀ r' ps', (∃ k, j + 1 ≤ k ∧ k < 32 ∧ a.getLsbD (31 - k) = true) →
      (∀ i, i ≠ B → i ≠ M → i ≠ P → i ≠ T1 → i ≠ T2 → r' i = r0 i) →
      lo (r' M) = 0x80000000#32 >>> (j + 1) → lo (r' B) = mulxN (j + 1) b →
      lo (r' P) = pAcc a b (j + 1) → Reach pl s0 Φ (mkS s0 (L + 20#64) r' ps')) :
    Reach pl s0 Φ (mkS s0 (L + 20#64) r ps) := by
  have hR' := hR
  obtain ⟨hA, hB, hM, hP, hQ', hT1, hT2, hBM, hBP, hBT1, hBT2, hMP, hMT1, hMT2, hPT1, hPT2, hT1T2,
    hAB, hAM, hAP, hAT1, hAT2, hQB, hQM, hQP, hQT1, hQT2⟩ := hR'
  have hrA : r A = r0 A := hr A hAB hAM hAP hAT1 hAT2
  have hrQ : r Q = r0 Q := hr Q hQB hQM hQP hQT1 hQT2
  refine reach_exec hrun hc.f5 (ex_tst (ne31 hM) (ne31 hA)) ?_
  rw [addr_eq L 20#64 4#64 24#64 rfl]
  refine reach_exec hrun hc.f6 ex_bcond ?_
  rw [hm, hrA, hA0]
  simp only [ConditionHolds, tstFlags_z]
  by_cases hbit : a.getLsbD (31 - j) = true
  · -- the bit for `x^j` is set: `p ^= b`, then test the remaining bits
    have hz : ¬ ((0x80000000#32 : BitVec 32) >>> j &&& a = 0#32) := by
      rw [m_and a j hj]; simp [hbit]
    simp only [hz, decide_false, Bool.false_eq_true, if_false]
    rw [addr_eq L 24#64 4#64 28#64 rfl]
    refine reach_exec hrun hc.f7 (ex_sub1 (ne31 hT1) (ne31 hM)) ?_
    rw [addr_eq L 28#64 4#64 32#64 rfl]
    refine reach_exec hrun hc.f8 (ex_eorw (ne31 hP) (ne31 hP) (ne31 hB)) ?_
    rw [addr_eq L 32#64 4#64 36#64 rfl]
    refine reach_exec hrun hc.f9 (ex_tst (ne31 hT1) (ne31 hA)) ?_
    rw [addr_eq L 36#64 4#64 40#64 rfl]
    refine reach_exec hrun hc.f10 ex_bcond ?_
    have eP : lo (Function.update r T1 (W (lo (r M) - 1#32)) P) = pAcc a b j := by
      rw [Function.update_of_ne hPT1]; exact hp
    have eB : lo (Function.update r T1 (W (lo (r M) - 1#32)) B) = mulxN j b := by
      rw [Function.update_of_ne hBT1]; exact hb
    have hpacc : pAcc a b j ^^^ mulxN j b = pAcc a b (j + 1) := by rw [pAcc_succ, if_pos hbit]
    simp only [Function.update_self, Function.update_of_ne hPT1, Function.update_of_ne hBT1,
      Function.update_of_ne hAT1, Function.update_of_ne hAP, Function.update_of_ne hPT1.symm, hp, hb,
      hpacc, lo_W, hrA, hA0, hm, ConditionHolds, tstFlags_z]
    by_cases hlow : ((0x80000000#32 : BitVec 32) >>> j - 1#32) &&& a = 0#32
    · -- no bits left: exit
      simp only [hlow, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
      rw [addr_eq L 40#64 4#64 44#64 rfl]
      refine hk _ _ ?_ ?_
      · intro i h1 h2 h3 h4 h5
        rw [Function.update_of_ne h3, Function.update_of_ne h4]; exact hr i h1 h2 h3 h4 h5
      · rw [Function.update_self, pAcc_eq_32 a b (j + 1) (by omega)]
        intro k hk1 hk2
        exact (m1_and a j hj).1 hlow k (by omega) hk2
    · -- more bits: back to the body
      simp only [hlow, decide_false, Bool.not_false, if_true]
      rw [show L + 40#64 + 0xffffffffffffffd8#64 = L by rw [BitVec.add_assoc]; bv_omega]
      obtain ⟨k, hk1, hk2, hk3⟩ : ∃ k, j < k ∧ k < 32 ∧ a.getLsbD (31 - k) = true := by
        by_contra hne
        apply hlow
        rw [m1_and a j hj]
        intro k h1 h2
        by_contra h3
        exact hne ⟨k, h1, h2, by simpa using h3⟩
      refine mm_body hrun hc hR (by rw [Function.update_of_ne hQP, Function.update_of_ne hQT1, hrQ, hQ0])
        (fun ps' => ?_)
      refine IH (by omega) _ _ ⟨k, by omega, hk2, hk3⟩ ?_ ?_ ?_ ?_
      · intro i h1 h2 h3 h4 h5
        simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3,
          Function.update_of_ne h4, Function.update_of_ne h5]
        exact hr i h1 h2 h3 h4 h5
      · rw [Function.update_of_ne hBM.symm, Function.update_of_ne hMT2, Function.update_self, lo_W,
          Function.update_of_ne hMP, Function.update_of_ne hMT1, hm, m_shr]
      · rw [Function.update_self, Function.update_of_ne hBP, Function.update_of_ne hBT1, hb,
          mulxN_succ, lo_W]
      · rw [Function.update_of_ne hBP.symm, Function.update_of_ne hPT2, Function.update_of_ne hMP.symm,
          Function.update_of_ne hPT1, Function.update_self, lo_W]
  · -- the bit is clear: straight back to the body
    have hz : (0x80000000#32 : BitVec 32) >>> j &&& a = 0#32 := by
      rw [m_and a j hj]; simpa using hbit
    simp only [hz, decide_true, if_true]
    rw [show L + 24#64 + 0xffffffffffffffe8#64 = L by rw [BitVec.add_assoc]; bv_omega]
    obtain ⟨k, hk1, hk2, hk3⟩ := hex
    have hkj : j < k := by
      rcases Nat.lt_or_eq_of_le hk1 with h | h
      · exact h
      · subst h; exact absurd hk3 hbit
    refine mm_body hrun hc hR (by rw [hrQ, hQ0]) (fun ps' => ?_)
    refine IH (by omega) _ _ ⟨k, by omega, hk2, hk3⟩ ?_ ?_ ?_ ?_
    · intro i h1 h2 h3 h4 h5
      simp only [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h4,
        Function.update_of_ne h5]
      exact hr i h1 h2 h3 h4 h5
    · rw [Function.update_of_ne hBM.symm, Function.update_of_ne hMT2, Function.update_self, lo_W,
        hm, m_shr]
    · rw [Function.update_self, lo_W, hb, mulxN_succ]
    · rw [Function.update_of_ne hBP.symm, Function.update_of_ne hPT2, Function.update_of_ne hMP.symm,
        Function.update_of_ne hPT1, hp, pAcc_succ, if_neg hbit]

/-- The whole loop, from the test at `L+0x14` with `m = 2^31`, `b`, `p = 0`. -/
theorem mm_loop (hrun : s0.status = .Running) (hc : MMCode pl s0.mem L A B M P Q T1 T2)
    (hR : MMRegs A B M P Q T1 T2) {a b : BitVec 32} {r0 : BitVec 5 → BitVec 64}
    (hk : ∀ r' ps', (∀ i, i ≠ B → i ≠ M → i ≠ P → i ≠ T1 → i ≠ T2 → r' i = r0 i) →
      r' P = W (pAcc a b 32) → Reach pl s0 Φ (mkS s0 (L + 44#64) r' ps'))
    (hA0 : lo (r0 A) = a) (hQ0 : lo (r0 Q) = POLY) :
    ∀ d j r ps, j + d = 31 → (∃ k, j ≤ k ∧ k < 32 ∧ a.getLsbD (31 - k) = true) →
      (∀ i, i ≠ B → i ≠ M → i ≠ P → i ≠ T1 → i ≠ T2 → r i = r0 i) →
      lo (r M) = 0x80000000#32 >>> j → lo (r B) = mulxN j b → lo (r P) = pAcc a b j →
      Reach pl s0 Φ (mkS s0 (L + 20#64) r ps) := by
  intro d
  induction d with
  | zero =>
    intro j r ps hjd hex hr hm hb hp
    exact mm_step hrun hc hR hk hA0 hQ0 (by omega) hex hr hm hb hp (fun h => by omega)
  | succ d ih =>
    intro j r ps hjd hex hr hm hb hp
    exact mm_step hrun hc hR hk hA0 hQ0 (by omega) hex hr hm hb hp
      (fun _ r' ps' hex' hr' hm' hb' hp' => ih (j + 1) r' ps' (by omega) hex' hr' hm' hb' hp')

/-- `a ≠ 0` has a set bit. -/
theorem exists_bit {a : BitVec 32} (ha : a ≠ 0#32) : ∃ k, 0 ≤ k ∧ k < 32 ∧ a.getLsbD (31 - k) = true := by
  by_contra h
  apply ha
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_zero]
  by_contra h2
  exact h ⟨31 - i, by omega, by omega, by rw [show 31 - (31 - i) = i by omega]; simpa using h2⟩

end loop

end ZlibCrc32.Small
end

section
/-! # Memory facts from the preconditions; read-only points-to is duplicable -/

namespace ZlibCrc32.Small

open Arm64 Arm64.Obj

theorem ro_union_left {h1 h2 : Heap} {a : BitVec 64} {b : BitVec 8}
    (h : h1.phys a = some (.ro b)) : (h1.union h2).phys a = some (.ro b) := by
  simp [Heap.union, h]

theorem ro_union_right {h1 h2 : Heap} (hd : h1.Disjoint h2) {a : BitVec 64} {b : BitVec 8}
    (h : h2.phys a = some (.ro b)) : (h1.union h2).phys a = some (.ro b) := by
  rcases hd.1 a with h0 | h0 | ⟨b', e1, e2⟩
  · simp [Heap.union, h0, h]
  · rw [h] at h0; cases h0
  · rw [h] at e2; cases e2; simp [Heap.union, e1]

theorem sep_left {P Q : SepProp} {h : Heap} (hs : (P ∗ Q).holds h) {a : BitVec 64} {b : BitVec 8}
    (hP : ∀ h1, P.holds h1 → h1.phys a = some (.ro b)) : h.phys a = some (.ro b) := by
  obtain ⟨h1, h2, _, rfl, p1, _⟩ := hs
  exact ro_union_left (hP h1 p1)

theorem sep_right {P Q : SepProp} {h : Heap} (hs : (P ∗ Q).holds h) {a : BitVec 64} {b : BitVec 8}
    (hQ : ∀ h2, Q.holds h2 → h2.phys a = some (.ro b)) : h.phys a = some (.ro b) := by
  obtain ⟨h1, h2, hd, rfl, _, q2⟩ := hs
  exact ro_union_right hd (hQ h2 q2)

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

theorem ro_matches {h : Heap} {m : Memory} (hm : h.Matches m) {a : BitVec 64} {b : BitVec 8}
    (hc : h.phys a = some (.ro b)) :
    m.read8 a = b ∧ (m.perm a).r = true ∧ m.isLazyFree a = false :=
  hm.1 a _ hc

/-- Readable bytes `bs` at `a`. -/
def RoBytes (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)) : Prop :=
  ∀ i (hi : i < bs.length), m.read8 (a + BitVec.ofNat 64 i) = bs[i] ∧
    (m.perm (a + BitVec.ofNat 64 i)).r = true ∧ m.isLazyFree (a + BitVec.ofNat 64 i) = false

theorem dataInit_eq (pl : Placement) :
    zlibCrc32Lib.dataInit pl =
      (pointsToBytesRO (pl.ρ "crc_table [zlib_crc32]") zlibCrc32PlacedData0 ∗
        (pointsToBytesRO (pl.ρ "crc_braid_table [zlib_crc32]") zlibCrc32PlacedData1 ∗
          pointsToBytesRO (pl.ρ "x2n_table [zlib_crc32]") zlibCrc32PlacedData2)) := by
  simp only [PlacedLib.dataInit, zlibCrc32Lib, zlibCrc32Data, List.map, sepAll,
    PlacedLib.patchedData, List.foldl, List.replicate, List.append_nil, if_true]

/-! ## Ghost-free read-only heaps -/

theorem empty_union (h : Heap) : Heap.empty.union h = h := by
  cases h; simp [Heap.union, Heap.empty]

theorem disjoint_empty (h : Heap) : Heap.empty.Disjoint h := by
  refine ⟨fun a => Or.inl rfl, fun γ k => Or.inl rfl, fun γ k => Or.inl rfl, ?_, fun a => Or.inl rfl⟩
  intro γ k oa v h
  rcases h with ⟨h, _⟩ | ⟨_, h⟩ <;> cases h

theorem pure_sep {φ : Prop} {P : SepProp} {h : Heap} (hφ : φ) (hP : P.holds h) :
    (⌜φ⌝ ∗ P).holds h :=
  ⟨Heap.empty, h, disjoint_empty h, (empty_union h).symm, ⟨rfl, hφ⟩, hP⟩

theorem pure_sep_elim {φ : Prop} {P : SepProp} {h : Heap} (hs : (⌜φ⌝ ∗ P).holds h) :
    φ ∧ P.holds h := by
  obtain ⟨h1, h2, _, rfl, ⟨rfl, hφ⟩, hP⟩ := hs
  exact ⟨hφ, by rwa [empty_union]⟩

/-- From `⌜φ⌝ ∗ D ∗ R` to `⌜ψ⌝ ∗ D ∗ R`, given `φ → ψ`. -/
theorem sat_pure_swap {φ ψ : Prop} {D R : SepProp} {m : Memory}
    (hs : m ⊨ (⌜φ⌝ ∗ D) ∗ R) (hψ : φ → ψ) : m ⊨ (⌜ψ⌝ ∗ D) ∗ R := by
  obtain ⟨h, ⟨h1, h2, hd, rfl, p1, r2⟩, hm⟩ := hs
  obtain ⟨hφ, hD⟩ := pure_sep_elim p1
  exact ⟨_, ⟨h1, h2, hd, rfl, pure_sep (hψ hφ) hD, r2⟩, hm⟩

theorem sat_pure {φ : Prop} {D R : SepProp} {m : Memory} (hs : m ⊨ (⌜φ⌝ ∗ D) ∗ R) : φ := by
  obtain ⟨h, ⟨h1, h2, hd, rfl, p1, r2⟩, hm⟩ := hs
  exact (pure_sep_elim p1).1

/-- The library's `x2n_table` bytes are readable, from `⌜φ⌝ ∗ dataInit ∗ R`. -/
theorem x2n_ro {φ : Prop} {pl : Placement} {R : SepProp} {m : Memory}
    (hs : m ⊨ (⌜φ⌝ ∗ zlibCrc32Lib.dataInit pl) ∗ R) :
    RoBytes m (pl.ρ "x2n_table [zlib_crc32]") zlibCrc32PlacedData2 := by
  obtain ⟨h, ⟨h1, h2, hd, rfl, p1, r2⟩, hm⟩ := hs
  obtain ⟨_, hD⟩ := pure_sep_elim p1
  rw [dataInit_eq] at hD
  intro i hi
  refine ro_matches hm (ro_union_left (sep_right hD fun k pk => ?_))
  exact sep_right pk fun k' pk' => ro_bytes _ _ k' pk' i hi

end ZlibCrc32.Small
end

section
/-! # From a reachability proof at the entry state to the subroutine outcome -/

namespace ZlibCrc32.Small

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

theorem fetch_off {pl : Placement} {m : Memory} (hP : zlibCrc32Lib.Placeable pl)
    (hCL : (prog pl).CodeLoaded m) (N k : Nat) {i : Instr} (hal : (N + k) % 4 = 0)
    (hlen : N + k + 4 ≤ 2824) (hr : zlibCrc32Text.relocAt? (N + k) = none)
    (hd : decode (zlibCrc32Text.wordAt (N + k)) = some i) :
    (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 N + BitVec.ofNat 64 k) = some i := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  exact fetch_plain hP hCL hal hlen hr hd

theorem pc_add (b : BitVec 64) (n k : Nat) :
    b + BitVec.ofNat 64 n + BitVec.ofNat 64 k = b + BitVec.ofNat 64 (n + k) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem W_xor (u v : BitVec 32) : W u ^^^ W v = W (u ^^^ v) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]

theorem holds32_W (v : BitVec 32) (p : Polynomial (ZMod 2)) (h : KadatchJenkins.regPoly v = p) :
    Holds32 (W v) p := by
  refine ⟨?_, ?_⟩
  · simp [W, BitVec.toNat_setWidth]; omega
  · rw [show BitVec.setWidth 32 (W v) = v from lo_W v]; exact h

theorem keep_of_agree5 {s0 : State} {r r1 : BitVec 5 → BitVec 64} {B M P T1 T2 : BitVec 5}
    (h1 : Keep s0 r1) (hB : B.toNat < 19) (hM : M.toNat < 19) (hP : P.toNat < 19)
    (hT1 : T1.toNat < 19) (hT2 : T2.toNat < 19)
    (h : ∀ i, i ≠ B → i ≠ M → i ≠ P → i ≠ T1 → i ≠ T2 → r i = r1 i) : Keep s0 r := by
  intro i hi
  have n : ∀ k : BitVec 5, k.toNat < 19 → i ≠ k := fun k hk e => by subst e; omega
  rw [h i (n B hB) (n M hM) (n P hP) (n T1 hT1) (n T2 hT2)]
  exact h1 i hi

theorem keep_self (s0 : State) : Keep s0 s0.regs.regs := fun _ _ => rfl

/-- A reachability proof from the entry state gives the subroutine outcome, once the
postcondition holds at every such final state. -/
theorem outcome_of_reach {α : Type} {spec : Spec α} {g : α} {R : SepProp} {pl : Placement}
    {s0 : State} {Φ : BitVec 64 → Prop} (hrun : s0.status = .Running) (h : Reach pl s0 Φ s0)
    (hpost : ∀ r ps, Φ (r 0#5) → Keep s0 r →
      (mkS s0 (s0.regs.regs 30#5) r ps).mem ⊨ spec.post g s0 (mkS s0 (s0.regs.regs 30#5) r ps) ∗ R) :
    ∃ sf, Steps (prog pl) s0 sf ∧ SubroutineOutcome spec g R s0 sf := by
  obtain ⟨sf, hs, r, ps, rfl, hX, hk⟩ := h
  refine ⟨_, hs, Or.inl ⟨⟨rfl, rfl, hrun⟩, ⟨rfl, ?_⟩, hpost r ps hX hk⟩⟩
  have e : ∀ k : BitVec 5, 19 ≤ k.toNat → k ≠ 31#5 →
      (mkS s0 (s0.regs.regs 30#5) r ps).readReg64 (.gpr k) = s0.readReg64 (.gpr k) := by
    intro k hk1 hk2
    rw [rd_gpr, if_neg hk2, hk k hk1]
    simp [State.readReg64, RegFile.read, hk2]
  exact ⟨e 19#5 (by decide) (by decide), e 20#5 (by decide) (by decide), e 21#5 (by decide) (by decide),
    e 22#5 (by decide) (by decide), e 23#5 (by decide) (by decide), e 24#5 (by decide) (by decide),
    e 25#5 (by decide) (by decide), e 26#5 (by decide) (by decide), e 27#5 (by decide) (by decide),
    e 28#5 (by decide) (by decide), e 29#5 (by decide) (by decide), rfl⟩

theorem reach_of_entry {pl : Placement} {s0 : State} {Φ : BitVec 64 → Prop}
    (h : Reach pl s0 Φ (mkS s0 s0.pc s0.regs.regs s0.pstate)) : Reach pl s0 Φ s0 := by
  rwa [mkS_self] at h

end ZlibCrc32.Small
end

section
/-! # The algebra of combining two CRC-32s -/

open Polynomial KadatchJenkins

namespace ZlibCrc32.Small

theorem length_ofBytes (bs : List (BitVec 8)) : (Message.ofBytes bs).length = 8 * bs.length := by
  induction bs with
  | nil => simp [Message.ofBytes]
  | cons b bs ih =>
    simp only [Message.ofBytes, List.flatMap_cons, List.length_append, List.length_ofFn] at ih ⊢
    rw [ih]; simp; ring

theorem stdU_degree : (stdU 32).degree < (crc32P.natDegree : WithBot ℕ) := by
  rw [crc32P_natDegree, Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  simp only [stdU, finsetSum_coeff, coeff_X_pow]
  apply Finset.sum_eq_zero
  intro k hk
  simp at hk
  rw [if_neg]; omega

theorem crc32P_natDegree_pos : 0 < crc32P.natDegree := by rw [crc32P_natDegree]; omega

/-- `P` does not divide `x^k`. -/
theorem xpow_mod_ne_zero (k : ℕ) : (X : (ZMod 2)[X]) ^ k % crc32P ≠ 0 := by
  intro h
  rw [EuclideanDomain.mod_eq_zero] at h
  have hXP : ¬ (X : (ZMod 2)[X]) ∣ crc32P := by
    rw [Polynomial.X_dvd_iff]
    simp [crc32P, coeff_X_pow, coeff_X, coeff_one]
  have hcop : IsCoprime (X : (ZMod 2)[X]) crc32P :=
    ((Polynomial.irreducible_X (R := ZMod 2)).coprime_iff_not_dvd).2 hXP
  have hu : IsUnit crc32P := (hcop.pow_left (m := k)).isUnit_of_dvd' h dvd_rfl
  have := Polynomial.natDegree_eq_zero_of_isUnit hu
  rw [crc32P_natDegree] at this
  omega

theorem ne_zero_of_regPoly {a : BitVec 32} {k : ℕ} (h : regPoly a = X ^ k % crc32P) : a ≠ 0#32 := by
  rintro rfl
  rw [regPoly_zero] at h
  exact xpow_mod_ne_zero k h.symm

/-- The statement `KadatchJenkins.crc_append_of_crcs`, as a hypothesis. -/
def CrcAppendOfCrcs : Prop :=
  ∀ (P u : (ZMod 2)[X]) (_ : 0 < P.natDegree) (_ : u.degree < (P.natDegree : WithBot ℕ))
    (M₁ M₂ : Message) (v v₁ v₂ : (ZMod 2)[X]),
    let v₁' := crc P u M₁ v₁ + ((v - v₁) * X ^ M₁.length) % P
    let v₂' := crc P u M₂ v₂ + ((v₁' - v₂) * X ^ M₂.length) % P
    v₁' = crc P u M₁ v ∧ v₂' = crc P u M₂ v₁' ∧ crc P u (M₁ ++ M₂) v = v₂'

/-- `crc2 ⊕ multmodp(op, crc1)` is the CRC-32 of the concatenation. -/
theorem combine_math (hKJ : CrcAppendOfCrcs) (A B : List (BitVec 8)) (c1 c2 op : BitVec 32)
    (h1 : regPoly c1 = crc32Poly 0#32 A) (h2 : regPoly c2 = crc32Poly 0#32 B)
    (hop : regPoly op = X ^ (8 * B.length) % crc32P) :
    regPoly (c2 ^^^ pAcc op c1 32) = crc32Poly 0#32 (A ++ B) := by
  have h := (hKJ crc32P (stdU 32) crc32P_natDegree_pos stdU_degree (Message.ofBytes A)
    (Message.ofBytes B) 0 0 0).2.2
  simp only [sub_self, zero_mul, EuclideanDomain.zero_mod, add_zero, sub_zero] at h
  rw [regPoly_xor, regPoly_pAcc_32, hop, h1, h2, mod_mul_mod]
  unfold crc32Poly
  have hcat : Message.ofBytes (A ++ B) = Message.ofBytes A ++ Message.ofBytes B := by
    simp [Message.ofBytes, List.flatMap_append]
  rw [regPoly_zero, hcat, h, length_ofBytes, mul_comm]

end ZlibCrc32.Small
end

section
/-! # Shared facts for `x2nmodp`: powers `x^(2^k)` are periodic in `k` with period 32, the
`x2n_table` load, and flag/bit facts about the loop counter -/

open Polynomial KadatchJenkins

namespace ZlibCrc32.Small

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

/-! ## Periodicity -/

/-- Repeated squaring of `x` in the reflected representation. -/
def sqChain : ℕ → BitVec 32
  | 0 => 0x40000000#32
  | j + 1 => pAcc (sqChain j) (sqChain j) 32

theorem regPoly_x : regPoly (0x40000000#32 : BitVec 32) = X := by
  ext n
  rw [coeff_regPoly, coeff_X]
  by_cases hn : n < 32
  · interval_cases n <;> decide
  · simp only [hn, false_and, if_false]; rw [if_neg]; omega

theorem X_mod : (X : (ZMod 2)[X]) % crc32P = X := by
  rw [← regPoly_x]; exact regPoly_mod _ le_rfl

theorem regPoly_sqChain (j : ℕ) : regPoly (sqChain j) = X ^ (2 ^ j) % crc32P := by
  induction j with
  | zero => simp [sqChain, regPoly_x, X_mod]
  | succ j ih =>
    rw [sqChain, regPoly_pAcc_32, ih, ← Polynomial.mul_mod, ← pow_add, pow_succ, mul_two]

theorem sqChain_32 : sqChain 32 = 0x40000000#32 := by decide +kernel

theorem pow_mod' (a : (ZMod 2)[X]) (n : ℕ) : a ^ n % crc32P = (a % crc32P) ^ n % crc32P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, Polynomial.mul_mod, ih, mod_mul_mod, mul_mod_mod]

theorem xpow32 : (X : (ZMod 2)[X]) ^ (2 ^ 32) % crc32P = X := by
  rw [← regPoly_sqChain, sqChain_32, regPoly_x]

theorem xpow_shift (m : ℕ) : (X : (ZMod 2)[X]) ^ (2 ^ (m + 32)) % crc32P = X ^ (2 ^ m) % crc32P := by
  rw [pow_add, mul_comm, pow_mul, pow_mod', xpow32]

theorem xpow_period (k : ℕ) : (X : (ZMod 2)[X]) ^ (2 ^ (k % 32)) % crc32P = X ^ (2 ^ k) % crc32P := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < 32
    · rw [Nat.mod_eq_of_lt hk]
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 32 := ⟨k - 32, by omega⟩
      rw [xpow_shift, show (m + 32) % 32 = m % 32 by omega]
      exact ih m (by omega)

/-- One step of `x2nmodp`: multiplying by the table entry for bit `i` of `n`. -/
theorem x2n_step (n i : ℕ) (a pv : BitVec 32)
    (ha : regPoly a = X ^ (2 ^ ((3 + i) % 32)) % crc32P)
    (hpv : regPoly pv = X ^ (8 * (n % 2 ^ i)) % crc32P) (hodd : n / 2 ^ i % 2 = 1) :
    regPoly (pAcc a pv 32) = X ^ (8 * (n % 2 ^ (i + 1))) % crc32P := by
  rw [regPoly_pAcc_32, ha, hpv, xpow_period, ← Polynomial.mul_mod, ← pow_add, Nat.mod_pow_succ, hodd]
  congr 2
  rw [pow_add]; ring

theorem x2n_skip (n i : ℕ) (pv : BitVec 32) (hpv : regPoly pv = X ^ (8 * (n % 2 ^ i)) % crc32P)
    (heven : n / 2 ^ i % 2 = 0) : regPoly pv = X ^ (8 * (n % 2 ^ (i + 1))) % crc32P := by
  rw [hpv, Nat.mod_pow_succ, heven]; simp

theorem regPoly_one : regPoly (0x80000000#32 : BitVec 32) = 1 := by
  ext n
  rw [coeff_regPoly, coeff_one]
  by_cases hn : n < 32
  · interval_cases n <;> decide
  · simp only [hn, false_and, if_false]; rw [if_neg]; omega

theorem one_mod : (1 : (ZMod 2)[X]) % crc32P = 1 := by
  rw [← regPoly_one]; exact regPoly_mod _ le_rfl

/-! ## The `x2n_table` load -/

theorem x2n_length : zlibCrc32PlacedData2.length = 128 := by decide +kernel

theorem read32_x2n {m : Memory} {T : BitVec 64} (ht : RoBytes m T zlibCrc32PlacedData2) (j : Nat)
    (hj : j < 32) :
    m.canRead (T + BitVec.ofNat 64 (4 * j)) 4 = true ∧
    m.read32 (T + BitVec.ofNat 64 (4 * j)) = word32 zlibCrc32PlacedData2 j := by
  have e : ∀ k, k < 4 → T + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 k =
      T + BitVec.ofNat 64 (4 * j + k) := fun k _ => pc_add _ _ _
  have r0 := ht (4 * j) (by rw [x2n_length]; omega)
  have r1 := ht (4 * j + 1) (by rw [x2n_length]; omega)
  have r2 := ht (4 * j + 2) (by rw [x2n_length]; omega)
  have r3 := ht (4 * j + 3) (by rw [x2n_length]; omega)
  rw [← e 1 (by omega)] at r1
  rw [← e 2 (by omega)] at r2
  rw [← e 3 (by omega)] at r3
  constructor
  · simp only [Memory.canRead, Memory.allPerm, Memory.allNoLazyFree, BitVec.add_assoc,
      BitVec.reduceAdd] at *
    simp [r0.2.1, r0.2.2, r1.2.1, r1.2.2, r2.2.1, r2.2.2, r3.2.1, r3.2.2]
  · simp only [Memory.read32, word32]
    have : T + BitVec.ofNat 64 (4 * j) + 0#64 = T + BitVec.ofNat 64 (4 * j) := by simp
    rw [this, r0.1, r1.1, r2.1, r3.1]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem, List.getElem?_eq_getElem, List.getElem?_eq_getElem,
      List.getElem?_eq_getElem]
    · rfl

/-! ## The loop counter -/

theorem subFlags_c (x y : BitVec 64) : (subFlags x y).c = decide (y.toNat ≤ x.toNat) := by
  simp only [subFlags, AddWithCarry64, BitVec.msb_eq_decide]
  simp [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_not]
  omega

theorem subFlags_z (x y : BitVec 64) : (subFlags x y).z = decide (x.toNat = y.toNat) := by
  simp only [subFlags, AddWithCarry64, if_true]
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, decide_eq_true_eq]
  rw [← BitVec.toNat_inj]
  simp [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_not]
  omega

theorem toNat_ofNat_lt (q : ℕ) (hq : q < 2 ^ 64) : (BitVec.ofNat 64 q).toNat = q :=
  Nat.mod_eq_of_lt hq

/-- `b.ls` after `cmp x, #1`, for `1 ≤ x`: taken iff `x = 1`. -/
theorem ls_cmp1 (q : ℕ) (hq1 : 1 ≤ q) (hq : q < 2 ^ 64) :
    ConditionHolds .LS (subFlags (BitVec.ofNat 64 q) 1#64) = decide (q = 1) := by
  simp only [ConditionHolds, subFlags_c, subFlags_z, toNat_ofNat_lt q hq]
  by_cases h : q = 1 <;> simp [h] <;> omega

theorem asr1_ofNat (q : ℕ) (hq : q < 2 ^ 63) :
    (BitVec.ofNat 64 q).sshiftRight 1 = BitVec.ofNat 64 (q / 2) := by
  have hmsb : (BitVec.ofNat 64 q).msb = false := by
    rw [BitVec.msb_eq_decide, toNat_ofNat_lt q (by omega)]; simp; omega
  rw [BitVec.sshiftRight_eq_of_msb_false hmsb]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, toNat_ofNat_lt q (by omega), toNat_ofNat_lt (q / 2) (by omega),
    Nat.shiftRight_eq_div_pow]

theorem getLsbD0_ofNat (q : ℕ) : (BitVec.ofNat 64 q).getLsbD 0 = decide (q % 2 = 1) := by
  rw [BitVec.getLsbD_ofNat, Nat.testBit_zero]
  simp

theorem add1_ofNat32 (k : ℕ) : BitVec.ofNat 32 k + 1#32 = BitVec.ofNat 32 (k + 1) := by
  rw [BitVec.ofNat_add]

theorem and31_ofNat32 (k : ℕ) : BitVec.ofNat 32 k &&& 0x1f#32 = BitVec.ofNat 32 (k % 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  simp only [BitVec.toNat_ofNat]
  rw [show 31 % 2 ^ 32 = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem idx_x2n (k : ℕ) (hk : k < 32) :
    W (lo (W (BitVec.ofNat 32 k))) <<< 2 = BitVec.ofNat 64 (4 * k) := by
  rw [lo_W]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

/-- The value of a 64-bit register whose signed reading is `n ≥ 0`. -/
theorem ofNat_of_toInt {x : BitVec 64} {n : ℕ} (h : x.toInt = (n : ℤ)) :
    x = BitVec.ofNat 64 n ∧ n < 2 ^ 63 := by
  have hc := BitVec.toInt_eq_toNat_cond x
  have hl := x.isLt
  split_ifs at hc with h2
  · have hx : x.toNat = n := by omega
    refine ⟨?_, by omega⟩
    apply BitVec.eq_of_toNat_eq; rw [hx, toNat_ofNat_lt n (by omega)]
  · omega

/-! ## Code shared by two exported copies -/

/-- The address of the function at block offset `G`. -/
def fA (pl : Placement) (G : Nat) : BitVec 64 := pl.base + BitVec.ofNat 64 G

/-- Fetch in a function present at two block offsets `G1`, `G2` with identical words. -/
theorem fetch2 {pl : Placement} {m : Memory} (hP : zlibCrc32Lib.Placeable pl)
    (hCL : (prog pl).CodeLoaded m) {G G1 G2 : Nat} (hG : G = G1 ∨ G = G2) (k : Nat) {i : Instr}
    (hk : (G1 + k) % 4 = 0 ∧ G1 + k + 4 ≤ 2824 ∧ (G2 + k) % 4 = 0 ∧ G2 + k + 4 ≤ 2824)
    (h : (zlibCrc32Text.relocAt? (G1 + k) = none ∧ decode (zlibCrc32Text.wordAt (G1 + k)) = some i) ∧
      (zlibCrc32Text.relocAt? (G2 + k) = none ∧ decode (zlibCrc32Text.wordAt (G2 + k)) = some i)) :
    (prog pl).fetchMem m (fA pl G + BitVec.ofNat 64 k) = some i := by
  unfold fA
  rcases hG with rfl | rfl
  · exact fetch_off hP hCL _ k hk.1 hk.2.1 h.1.1 h.1.2
  · exact fetch_off hP hCL _ k hk.2.2.1 hk.2.2.2 h.2.1 h.2.2

theorem fetch2' {pl : Placement} {m : Memory} (hP : zlibCrc32Lib.Placeable pl)
    (hCL : (prog pl).CodeLoaded m) {G G1 G2 : Nat} (hG : G = G1 ∨ G = G2) (a b : Nat) {i : Instr}
    (hk : (G1 + (a + b)) % 4 = 0 ∧ G1 + (a + b) + 4 ≤ 2824 ∧ (G2 + (a + b)) % 4 = 0 ∧
      G2 + (a + b) + 4 ≤ 2824)
    (h : (zlibCrc32Text.relocAt? (G1 + (a + b)) = none ∧
        decode (zlibCrc32Text.wordAt (G1 + (a + b))) = some i) ∧
      (zlibCrc32Text.relocAt? (G2 + (a + b)) = none ∧
        decode (zlibCrc32Text.wordAt (G2 + (a + b))) = some i)) :
    (prog pl).fetchMem m (fA pl G + BitVec.ofNat 64 a + BitVec.ofNat 64 b) = some i := by
  rw [pc_add]; exact fetch2 hP hCL hG (a + b) hk h

theorem fA_add (pl : Placement) (G k : Nat) : fA pl G + BitVec.ofNat 64 k = pl.base + BitVec.ofNat 64 (G + k) :=
  pc_add _ _ _

end ZlibCrc32.Small
end

section
/-! # Decoding relocated `ADRP`/`ADD`/`ADR` words: the register-independent part

From the byte-table pilot proof. -/

namespace ZlibCrc32.Small

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

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

theorem page_add_lo (T : BitVec 64) : pageOf T + (T.extractLsb' 0 12).setWidth 64 = T := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, pageOf_toNat]
  simp [BitVec.toNat_setWidth, BitVec.extractLsb'_toNat]
  have := T.isLt; omega


theorem decode_nop : decode nopWord = some .nop := by decide


theorem awc_add' (x y : BitVec 64) :
    BitVec.truncate 64 (0#65 + (BitVec.zeroExtend 65 y + BitVec.zeroExtend 65 x)) = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_setWidth]
  omega

end ZlibCrc32.Small
end

section
/-! # Relocated `ADRP x11, x2n_table` + `ADD x11, x11, :lo12:` pair(s) at offsets 2072/2276 (generated) -/

namespace ZlibCrc32.Small

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

abbrev symCmb : String := "x2n_table [zlib_crc32]"

theorem pw_adrpCmb (pl : Placement) (o : Nat) (ho : o = 2072 ∨ o = 2276) :
    zlibCrc32Text.patchedWord pl o =
      if pl.relax o then nopWord else adrpWord 0x9000000b#32 (pl.base + BitVec.ofNat 64 o) (pl.ρ symCmb) := by
  have hr : zlibCrc32Text.relocAt? o = some { off := o, kind := .adrpHi21, sym := symCmb } := by
    rcases ho with rfl | rfl <;> rfl
  have h1 : zlibCrc32Text.relaxableAt o = true := by rcases ho with rfl | rfl <;> decide +kernel
  have h2 : zlibCrc32Text.relaxableAt (o - 4) = false := by rcases ho with rfl | rfl <;> decide +kernel
  have hw : zlibCrc32Text.wordAt o = 0x9000000b#32 := by rcases ho with rfl | rfl <;> decide +kernel
  have hlk : lookup symCmb zlibCrc32Text.symbols = none := by decide
  cases h : pl.relax o <;> rcases ho with rfl | rfl <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h1, h2, hr, hw,
      CodeBlock.relocTarget, CodeBlock.b2bNext?, CodeBlock.undefWeakBranch, CodeBlock.target,
      CodeBlock.resolve, hlk, addSignedAddr, patchRelocWord, RelocKind.isGotOrTlsIe]

theorem pw_addCmb (pl : Placement) (o : Nat) (ho : o = 2072 ∨ o = 2276) :
    zlibCrc32Text.patchedWord pl (o + 4) =
      if pl.relax o then adrWord (adrTemplate 0x9100016b#32) (pl.base + BitVec.ofNat 64 (o + 4)) (pl.ρ symCmb)
      else lo12Word 0 0x9100016b#32 (pl.ρ symCmb) := by
  have hr : zlibCrc32Text.relocAt? (o + 4) = some { off := o + 4, kind := .addLo12, sym := symCmb } := by
    rcases ho with rfl | rfl <;> rfl
  have h1 : zlibCrc32Text.relaxableAt o = true := by rcases ho with rfl | rfl <;> decide +kernel
  have h2 : zlibCrc32Text.relaxableAt (o + 4) = false := by rcases ho with rfl | rfl <;> decide +kernel
  have hw : zlibCrc32Text.wordAt (o + 4) = 0x9100016b#32 := by rcases ho with rfl | rfl <;> decide +kernel
  have hlk : lookup symCmb zlibCrc32Text.symbols = none := by decide
  have h4 : (4 ≤ o + 4) = True := by simp
  cases h : pl.relax o <;> rcases ho with rfl | rfl <;>
    simp [CodeBlock.patchedWord, CodeBlock.relaxedAt, h, h1, h2, hr, hw, h4,
      CodeBlock.relocTarget, CodeBlock.b2bNext?, CodeBlock.undefWeakBranch, CodeBlock.target,
      CodeBlock.resolve, hlk, addSignedAddr, patchRelocWord, RelocKind.isGotOrTlsIe]

section words
variable (D : BitVec 64)

theorem wA_maskCmb : adrpWordOff 0x9000000b#32 D &&& 0x1f000000#32 = 0x10000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wA_31Cmb : (adrpWordOff 0x9000000b#32 D).getLsbD 31 = true := by
  simp [adrpWordOff]

theorem wA_rdCmb : (adrpWordOff 0x9000000b#32 D).extractLsb' 0 5 = 11#5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wA_offCmb (hlo : ∀ i, i < 12 → D.getLsbD i = false)
    (hhi : ∀ i, 32 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 32) :
    ((adrpWordOff 0x9000000b#32 D).extractLsb' 5 19 ++
      (adrpWordOff 0x9000000b#32 D).extractLsb' 29 2).signExtend 64 <<< 12 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrpWordOff, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getMsbD]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | exact hlo _ (by omega) | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm

theorem wC_maskCmb : adrWordOff 0x1000000b#32 D &&& 0x1f000000#32 = 0x10000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wC_31Cmb : (adrWordOff 0x1000000b#32 D).getLsbD 31 = false := by
  simp [adrWordOff]

theorem wC_rdCmb : (adrWordOff 0x1000000b#32 D).extractLsb' 0 5 = 11#5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wC_offCmb (hhi : ∀ i, 20 ≤ i → i < 64 → D.getLsbD i = D.getLsbD 20) :
    ((adrWordOff 0x1000000b#32 D).extractLsb' 5 19 ++
      (adrWordOff 0x1000000b#32 D).extractLsb' 29 2).signExtend 64 = D := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [adrWordOff, BitVec.getLsbD_signExtend, BitVec.getLsbD_append,
    BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.msb_append, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp <;> (try simp only [← BitVec.getLsbD_eq_getElem]) <;>
    first | rfl | exact hhi _ (by omega) (by omega) |
      exact (hhi _ (by omega) (by omega)).symm

theorem wB_maskCmb : lo12Word 0 0x9100016b#32 D &&& 0x1f800000#32 = 0x11000000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  interval_cases i <;> simp

theorem wB_bitsCmb : (lo12Word 0 0x9100016b#32 D).getLsbD 31 = true ∧
    (lo12Word 0 0x9100016b#32 D).getLsbD 30 = false ∧
    (lo12Word 0 0x9100016b#32 D).getLsbD 29 = false ∧
    (lo12Word 0 0x9100016b#32 D).getLsbD 22 = false := by
  simp [lo12Word]

theorem wB_rdCmb : (lo12Word 0 0x9100016b#32 D).extractLsb' 0 5 = 11#5 ∧
    (lo12Word 0 0x9100016b#32 D).extractLsb' 5 5 = 11#5 := by
  constructor <;>
  · apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
      BitVec.getLsbD_shiftLeft]
    interval_cases i <;> simp

theorem wB_immCmb : (lo12Word 0 0x9100016b#32 D).extractLsb' 10 12 = D.extractLsb' 0 12 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [lo12Word, BitVec.getLsbD_extractLsb', BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth]
  interval_cases i <;> simp

end words

theorem decode_ACmb {P T : BitVec 64} (hr : AdrpInRange P T) :
    decode (adrpWord 0x9000000b#32 P T) = some (.adr true (.gpr 11#5) (pageOf T - pageOf P)) := by
  rw [adrpWord, decode_adr_class _ (wA_maskCmb _), wA_31Cmb, wA_rdCmb,
    wA_offCmb _ (lo_bits T P) (hi_bits32 _ hr.1 hr.2)]
  rfl

theorem decode_CCmb {P T : BitVec 64} (hr : AdrInRange P T) :
    decode (adrWord (adrTemplate 0x9100016b#32) P T) = some (.adr false (.gpr 11#5) (T - P)) := by
  rw [adrWord, show adrTemplate 0x9100016b#32 = 0x1000000b#32 by decide,
    decode_adr_class _ (wC_maskCmb _), wC_31Cmb, wC_rdCmb, if_neg (by decide), wC_offCmb _ (hi_bits20 _ hr.1 hr.2)]
  rfl

theorem decode_BCmb (T : BitVec 64) :
    decode (lo12Word 0 0x9100016b#32 T) =
      some (.addSubImm .W64 .ADD (.gpr 11#5) (.gpr 11#5) (T.extractLsb' 0 12) false) := by
  obtain ⟨b31, b30, b29, b22⟩ := wB_bitsCmb T
  rw [decode_addimm_class _ (wB_maskCmb _), b31, b30, b29, b22, wB_rdCmb T |>.1, wB_rdCmb T |>.2, wB_immCmb]
  rfl

theorem targetCmb (pl : Placement) (o : Nat) (k : RelocKind) :
    zlibCrc32Text.target pl { off := o, kind := k, sym := symCmb } = pl.ρ symCmb := by
  have hlk : lookup symCmb zlibCrc32Text.symbols = none := by decide
  simp [CodeBlock.target, CodeBlock.resolve, hlk, addSignedAddr]

theorem range_adrpCmb {pl : Placement} (hP : zlibCrc32Lib.Placeable pl) (o : Nat) (ho : o = 2072 ∨ o = 2276) :
    AdrpInRange (pl.base + BitVec.ofNat 64 o) (pl.ρ symCmb) := by
  have hmem : ({ off := o, kind := .adrpHi21, sym := symCmb } : RelocEntry) ∈ zlibCrc32Text.relocs := by
    rcases ho with rfl | rfl <;> decide
  have h := (hP.text.relocs_ok _ hmem).2.2
  have ht : zlibCrc32Text.relocTarget pl o { off := o, kind := .adrpHi21, sym := symCmb } = pl.ρ symCmb := by
    simp only [CodeBlock.relocTarget, CodeBlock.b2bNext?]
    simp [targetCmb]
  simp only [zlibCrc32Lib] at h
  rw [ht] at h
  exact h

theorem range_adrCmb {pl : Placement} (hP : zlibCrc32Lib.Placeable pl) (o : Nat) (ho : o = 2072 ∨ o = 2276)
    (hrel : pl.relax o = true) :
    AdrInRange (pl.base + BitVec.ofNat 64 (o + 4)) (pl.ρ symCmb) := by
  have h1 : zlibCrc32Text.relaxableAt o = true := by rcases ho with rfl | rfl <;> decide +kernel
  have hr : zlibCrc32Text.relocAt? (o + 4) = some { off := o + 4, kind := .addLo12, sym := symCmb } := by
    rcases ho with rfl | rfl <;> rfl
  have hPt : zlibCrc32Text.Placeable pl := hP.text
  have h := hPt.relaxed_ok o _ (by simp [CodeBlock.relaxedAt, h1, hrel]) hr
  rwa [targetCmb] at h

/-- Both forms of the pair load the object's address into `x11`. -/
theorem steps_pairCmb {pl : Placement} {s0 : State} {r : BitVec 5 → BitVec 64} {ps : PState}
    (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded s0.mem)
    (hrun : s0.status = .Running) (o : Nat) (ho : o = 2072 ∨ o = 2276) :
    Steps (prog pl) (mkS s0 (pl.base + BitVec.ofNat 64 o) r ps)
      (mkS s0 (pl.base + BitVec.ofNat 64 (o + 8)) (Function.update r 11#5 (pl.ρ symCmb)) ps) := by
  have hal : o % 4 = 0 := by rcases ho with rfl | rfl <;> rfl
  have hle : o + 8 ≤ 2824 := by rcases ho with rfl | rfl <;> decide
  have hf2 := fetch_word hP hCL (off := o + 4) (by omega) (by omega)
  rw [pw_addCmb pl o ho] at hf2
  have hf1 := fetch_word hP hCL (off := o) hal (by omega)
  rw [pw_adrpCmb pl o ho] at hf1
  have p4 : pl.base + BitVec.ofNat 64 o + 4#64 = pl.base + BitVec.ofNat 64 (o + 4) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have p8 : pl.base + BitVec.ofNat 64 (o + 4) + 4#64 = pl.base + BitVec.ofNat 64 (o + 8) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show o + 4 + 4 = o + 8 by omega]
  have hrd : (11#5 : BitVec 5) ≠ 31#5 := by decide
  cases h : pl.relax o
  · simp only [h, Bool.false_eq_true, if_false] at hf1 hf2
    rw [decode_ACmb (range_adrpCmb hP o ho)] at hf1
    rw [decode_BCmb] at hf2
    have st1 := step_mkS (r := r) (ps := ps) hrun hf1
    have e1 : execInstWithSvc (evalSvc Syscall.standard)
        (.adr true (.gpr 11#5) (pageOf (pl.ρ symCmb) - pageOf (pl.base + BitVec.ofNat 64 o)))
        (mkS s0 (pl.base + BitVec.ofNat 64 o) r ps) =
        mkS s0 (pl.base + BitVec.ofNat 64 (o + 4)) (Function.update r 11#5 (pageOf (pl.ρ symCmb))) ps := by
      show State.advancePC (State.writeReg64 _ _ _) = _
      rw [wr_gpr _ _ _ _ _ _ hrd, mkS_advancePC, p4]
      congr 2
      have e : ∀ a b : BitVec 64, a + (b - a) = b := by intro a b; bv_omega
      simp only [mkS_pc, if_true]
      rw [show (pl.base + BitVec.ofNat 64 o) &&& 0xfffffffffffff000#64 =
        pageOf (pl.base + BitVec.ofNat 64 o) from rfl, e]
    rw [e1] at st1
    have st2 := step_mkS (r := Function.update r 11#5 (pageOf (pl.ρ symCmb))) (ps := ps) hrun hf2
    have e2 : execInstWithSvc (evalSvc Syscall.standard)
        (.addSubImm .W64 .ADD (.gpr 11#5) (.gpr 11#5) ((pl.ρ symCmb).extractLsb' 0 12) false)
        (mkS s0 (pl.base + BitVec.ofNat 64 (o + 4)) (Function.update r 11#5 (pageOf (pl.ρ symCmb))) ps) =
        mkS s0 (pl.base + BitVec.ofNat 64 (o + 8)) (Function.update r 11#5 (pl.ρ symCmb)) ps := by
      show State.advancePC (State.writeReg _ _ _ _) = _
      simp only [State.writeReg, State.readReg, rd_gpr, hrd, if_false, Function.update_self,
        evalAddSub, Bool.false_eq_true]
      rw [wr_gpr _ _ _ _ _ _ hrd, mkS_advancePC, p8, Function.update_idem]
      congr 2
      rw [awc_add']
      exact page_add_lo _
    rw [e2] at st2
    exact Steps.step st1 (Steps.step st2 (Steps.refl _))
  · simp only [h, if_true] at hf1 hf2
    rw [decode_nop] at hf1
    rw [decode_CCmb (range_adrCmb hP o ho h)] at hf2
    have st1 := step_mkS (r := r) (ps := ps) hrun hf1
    rw [show execInstWithSvc (evalSvc Syscall.standard) .nop (mkS s0 (pl.base + BitVec.ofNat 64 o) r ps) =
      mkS s0 (pl.base + BitVec.ofNat 64 o + 4#64) r ps from rfl, p4] at st1
    have st2 := step_mkS (r := r) (ps := ps) hrun hf2
    have e2 : execInstWithSvc (evalSvc Syscall.standard)
        (.adr false (.gpr 11#5) (pl.ρ symCmb - (pl.base + BitVec.ofNat 64 (o + 4))))
        (mkS s0 (pl.base + BitVec.ofNat 64 (o + 4)) r ps) =
        mkS s0 (pl.base + BitVec.ofNat 64 (o + 8)) (Function.update r 11#5 (pl.ρ symCmb)) ps := by
      show State.advancePC (State.writeReg64 _ _ _) = _
      rw [wr_gpr _ _ _ _ _ _ hrd, mkS_advancePC, p8]
      congr 2
      simp only [mkS_pc, Bool.false_eq_true, if_false]
      bv_omega
    rw [e2] at st2
    exact Steps.step st1 (Steps.step st2 (Steps.refl _))

end ZlibCrc32.Small
end

section
/-! # `crc32_combine(crc1, crc2, len2) = multmodp(x2nmodp(len2, 3), crc1) ^ crc2`, at block
offsets 2256 (`crc32_combine`) and 2052 (`crc32_combine64`, the same words)

```
+0x00 mov  w8, #0x8320           +0x3c tbz  w2, #0, +0x20
+0x04 movk w8, #0xedb8, lsl 16   +0x40 and  w13, w10, #0x1f
+0x08 cbz  x2, +0x84             +0x44 mov  w9, wzr
+0x0c mov  w10, #3               +0x48 mov  w14, #0x80000000
+0x10 mov  w12, #0x80000000      +0x4c ldr  w13, [x11, w13, uxtw #2]
+0x14 adrp x11, x2n_table        +0x50 b    +0x68
+0x18 add  x11, x11, :lo12:      +0x54 .. +0x7c multmodp (a = w13, b = w12, m = w14, p = w9)
+0x1c b    +0x3c                 +0x80 b    +0x24
+0x20 mov  w9, w12               +0x84 mov  w9, #0x80000000
+0x24 asr  x13, x2, #1           +0x88 mov  w10, wzr
+0x28 cmp  x2, #1                +0x8c mov  w11, #0x80000000
+0x2c add  w10, w10, #1          +0x90 b    +0xa8
+0x30 mov  w12, w9               +0x94 .. +0xbc multmodp (a = w9, b = w0, m = w11, p = w10)
+0x34 mov  x2, x13               +0xc0 mov  w8, w1
+0x38 b.ls +0x88                 +0xc4 eor  x0, x8, x10
                                 +0xc8 ret
``` -/

open Polynomial KadatchJenkins

namespace ZlibCrc32.Small

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

section
variable {pl : Placement} {m : Memory} (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded m)
  {C : Nat} (hC : C = 2256 ∨ C = 2052)
include hP hCL hC

theorem cf (k : Nat) {i : Instr}
    (hk : (2256 + k) % 4 = 0 ∧ 2256 + k + 4 ≤ 2824 ∧ (2052 + k) % 4 = 0 ∧ 2052 + k + 4 ≤ 2824)
    (h : (zlibCrc32Text.relocAt? (2256 + k) = none ∧ decode (zlibCrc32Text.wordAt (2256 + k)) = some i) ∧
      (zlibCrc32Text.relocAt? (2052 + k) = none ∧ decode (zlibCrc32Text.wordAt (2052 + k)) = some i)) :
    (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 k) = some i := fetch2 hP hCL hC k hk h

theorem c0 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 0) =
    some (.moveWide .W32 .MOVZ (.gpr 8#5) 0x8320#16 0) := cf hP hCL hC 0 (by decide) (by decide +kernel)
theorem c4 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 4) =
    some (.moveWide .W32 .MOVK (.gpr 8#5) 0xedb8#16 16) := cf hP hCL hC 4 (by decide) (by decide +kernel)
theorem c8 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 8) =
    some (.cbz .W64 false (.gpr 2#5) 0x7c#64) := cf hP hCL hC 8 (by decide) (by decide +kernel)
theorem c12 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 12) =
    some (.moveWide .W32 .MOVZ (.gpr 10#5) 0x0003#16 0) := cf hP hCL hC 12 (by decide) (by decide +kernel)
theorem c16 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 16) =
    some (.moveWide .W32 .MOVZ (.gpr 12#5) 0x8000#16 16) := cf hP hCL hC 16 (by decide) (by decide +kernel)
theorem c28 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 28) =
    some (.b 0x20#64) := cf hP hCL hC 28 (by decide) (by decide +kernel)
theorem c32 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 32) =
    some (.logicalShift .W32 .ORR (.gpr 9#5) .xzr (.gpr 12#5) .LSL 0) := cf hP hCL hC 32 (by decide) (by decide +kernel)
theorem c36 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 36) =
    some (.bitfield .W64 .SBFM (.gpr 13#5) (.gpr 2#5) 1 63) := cf hP hCL hC 36 (by decide) (by decide +kernel)
theorem c40 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 40) =
    some (.addSubImm .W64 .SUBS .xzr (.gpr 2#5) 0x001#12 false) := cf hP hCL hC 40 (by decide) (by decide +kernel)
theorem c44 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 44) =
    some (.addSubImm .W32 .ADD (.gpr 10#5) (.gpr 10#5) 0x001#12 false) := cf hP hCL hC 44 (by decide) (by decide +kernel)
theorem c48 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 48) =
    some (.logicalShift .W32 .ORR (.gpr 12#5) .xzr (.gpr 9#5) .LSL 0) := cf hP hCL hC 48 (by decide) (by decide +kernel)
theorem c52 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 52) =
    some (.logicalShift .W64 .ORR (.gpr 2#5) .xzr (.gpr 13#5) .LSL 0) := cf hP hCL hC 52 (by decide) (by decide +kernel)
theorem c56 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 56) =
    some (.bCond .LS 0x50#64) := cf hP hCL hC 56 (by decide) (by decide +kernel)
theorem c60 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 60) =
    some (.tbz .W32 false (.gpr 2#5) 0 0xffffffffffffffe4#64) := cf hP hCL hC 60 (by decide) (by decide +kernel)
theorem c64 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 64) =
    some (.logicalImm .W32 .AND (.gpr 13#5) (.gpr 10#5) 0x0000001f0000001f#64) := cf hP hCL hC 64 (by decide) (by decide +kernel)
theorem c68 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 68) =
    some (.logicalShift .W32 .ORR (.gpr 9#5) .xzr .xzr .LSL 0) := cf hP hCL hC 68 (by decide) (by decide +kernel)
theorem c72 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 72) =
    some (.moveWide .W32 .MOVZ (.gpr 14#5) 0x8000#16 16) := cf hP hCL hC 72 (by decide) (by decide +kernel)
theorem c76 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 76) =
    some (.ldr .W32 .W32 false (.gpr 13#5) (.RegOffset (.gpr 11#5) (.gpr 13#5) .UXTW 2)) :=
  cf hP hCL hC 76 (by decide) (by decide +kernel)
theorem c80 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 80) =
    some (.b 0x18#64) := cf hP hCL hC 80 (by decide) (by decide +kernel)
theorem c128 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 128) =
    some (.b 0xffffffffffffffa4#64) := cf hP hCL hC 128 (by decide) (by decide +kernel)
theorem c132 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 132) =
    some (.moveWide .W32 .MOVZ (.gpr 9#5) 0x8000#16 16) := cf hP hCL hC 132 (by decide) (by decide +kernel)
theorem c136 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 136) =
    some (.logicalShift .W32 .ORR (.gpr 10#5) .xzr .xzr .LSL 0) := cf hP hCL hC 136 (by decide) (by decide +kernel)
theorem c140 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 140) =
    some (.moveWide .W32 .MOVZ (.gpr 11#5) 0x8000#16 16) := cf hP hCL hC 140 (by decide) (by decide +kernel)
theorem c144 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 144) =
    some (.b 0x18#64) := cf hP hCL hC 144 (by decide) (by decide +kernel)
theorem c192 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 192) =
    some (.logicalShift .W32 .ORR (.gpr 8#5) .xzr (.gpr 1#5) .LSL 0) := cf hP hCL hC 192 (by decide) (by decide +kernel)
theorem c196 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 196) =
    some (.logicalShift .W64 .EOR (.gpr 0#5) (.gpr 8#5) (.gpr 10#5) .LSL 0) := cf hP hCL hC 196 (by decide) (by decide +kernel)
theorem c200 : (prog pl).fetchMem m (fA pl C + BitVec.ofNat 64 200) =
    some (.ret (.gpr 30#5)) := cf hP hCL hC 200 (by decide) (by decide +kernel)

theorem mmcode_c1 : MMCode pl m (fA pl C + BitVec.ofNat 64 84) 13#5 12#5 14#5 9#5 8#5 15#5 16#5 where
  f0 := cf hP hCL hC 84 (by decide) (by decide +kernel)
  f1 := fetch2' hP hCL hC 84 4 (by decide) (by decide +kernel)
  f2 := fetch2' hP hCL hC 84 8 (by decide) (by decide +kernel)
  f3 := fetch2' hP hCL hC 84 12 (by decide) (by decide +kernel)
  f4 := fetch2' hP hCL hC 84 16 (by decide) (by decide +kernel)
  f5 := fetch2' hP hCL hC 84 20 (by decide) (by decide +kernel)
  f6 := fetch2' hP hCL hC 84 24 (by decide) (by decide +kernel)
  f7 := fetch2' hP hCL hC 84 28 (by decide) (by decide +kernel)
  f8 := fetch2' hP hCL hC 84 32 (by decide) (by decide +kernel)
  f9 := fetch2' hP hCL hC 84 36 (by decide) (by decide +kernel)
  f10 := fetch2' hP hCL hC 84 40 (by decide) (by decide +kernel)

theorem mmcode_c2 : MMCode pl m (fA pl C + BitVec.ofNat 64 148) 9#5 0#5 11#5 10#5 8#5 12#5 13#5 where
  f0 := cf hP hCL hC 148 (by decide) (by decide +kernel)
  f1 := fetch2' hP hCL hC 148 4 (by decide) (by decide +kernel)
  f2 := fetch2' hP hCL hC 148 8 (by decide) (by decide +kernel)
  f3 := fetch2' hP hCL hC 148 12 (by decide) (by decide +kernel)
  f4 := fetch2' hP hCL hC 148 16 (by decide) (by decide +kernel)
  f5 := fetch2' hP hCL hC 148 20 (by decide) (by decide +kernel)
  f6 := fetch2' hP hCL hC 148 24 (by decide) (by decide +kernel)
  f7 := fetch2' hP hCL hC 148 28 (by decide) (by decide +kernel)
  f8 := fetch2' hP hCL hC 148 32 (by decide) (by decide +kernel)
  f9 := fetch2' hP hCL hC 148 36 (by decide) (by decide +kernel)
  f10 := fetch2' hP hCL hC 148 40 (by decide) (by decide +kernel)

end

theorem cstep (pl : Placement) (C k : Nat) :
    fA pl C + BitVec.ofNat 64 k + 4#64 = fA pl C + BitVec.ofNat 64 (k + 4) := pc_add _ _ _

theorem cjump (pl : Placement) (C a b c : Nat) (h : (a + b) % 2 ^ 64 = c % 2 ^ 64) :
    fA pl C + BitVec.ofNat 64 a + BitVec.ofNat 64 b = fA pl C + BitVec.ofNat 64 c := by
  rw [pc_add]; congr 1; apply BitVec.eq_of_toNat_eq; simpa using h

/-- The result: `crc2 ^ multmodp(op, crc1)` for an operator `op` with polynomial `x^(8n) mod P`. -/
def CmbOk (c1 c2 : BitVec 32) (n : ℕ) (x : BitVec 64) : Prop :=
  ∃ op : BitVec 32, regPoly op = X ^ (8 * n) % crc32P ∧ x = W (c2 ^^^ pAcc op c1 32)

/-- The registers the `x2nmodp` part carries through: table, `POLY`, `crc1`, `crc2`. -/
def CInv (pl : Placement) (s0 : State) (c1 c2 : BitVec 32) (r : BitVec 5 → BitVec 64) : Prop :=
  r 11#5 = pl.ρ "x2n_table [zlib_crc32]" ∧ lo (r 8#5) = POLY ∧ lo (r 0#5) = c1 ∧ lo (r 1#5) = c2 ∧
    Keep s0 r

theorem cinv_update {pl : Placement} {s0 : State} {c1 c2 : BitVec 32} {r : BitVec 5 → BitVec 64}
    (h : CInv pl s0 c1 c2 r) {d : BitVec 5}
    (hd : d ≠ 11#5 ∧ d ≠ 8#5 ∧ d ≠ 0#5 ∧ d ≠ 1#5 ∧ d.toNat < 19) (v : BitVec 64) :
    CInv pl s0 c1 c2 (Function.update r d v) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨e1, e2, e3, e4, e5⟩ := hd
  refine ⟨?_, ?_, ?_, ?_, keep_update h5 e5 v⟩
  · rw [Function.update_of_ne (Ne.symm e1)]; exact h1
  · rw [Function.update_of_ne (Ne.symm e2)]; exact h2
  · rw [Function.update_of_ne (Ne.symm e3)]; exact h3
  · rw [Function.update_of_ne (Ne.symm e4)]; exact h4

theorem cinv_agree {pl : Placement} {s0 : State} {c1 c2 : BitVec 32} {r r' : BitVec 5 → BitVec 64}
    (h : CInv pl s0 c1 c2 r) {B M P T1 T2 : BitVec 5}
    (hS : ∀ j : BitVec 5, (j = B ∨ j = M ∨ j = P ∨ j = T1 ∨ j = T2) →
      j ≠ 11#5 ∧ j ≠ 8#5 ∧ j ≠ 0#5 ∧ j ≠ 1#5 ∧ j.toNat < 19)
    (hr : ∀ i, i ≠ B → i ≠ M → i ≠ P → i ≠ T1 → i ≠ T2 → r' i = r i) : CInv pl s0 c1 c2 r' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hB := hS B (Or.inl rfl)
  have hM := hS M (Or.inr (Or.inl rfl))
  have hP := hS P (Or.inr (Or.inr (Or.inl rfl)))
  have hT1 := hS T1 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hT2 := hS T2 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  have g : ∀ k : BitVec 5, k ≠ B → k ≠ M → k ≠ P → k ≠ T1 → k ≠ T2 → r' k = r k := hr
  refine ⟨?_, ?_, ?_, ?_, keep_of_agree5 h5 hB.2.2.2.2 hM.2.2.2.2 hP.2.2.2.2 hT1.2.2.2.2 hT2.2.2.2.2 hr⟩
  · rw [g _ hB.1.symm hM.1.symm hP.1.symm hT1.1.symm hT2.1.symm]; exact h1
  · rw [g _ hB.2.1.symm hM.2.1.symm hP.2.1.symm hT1.2.1.symm hT2.2.1.symm]; exact h2
  · rw [g _ hB.2.2.1.symm hM.2.2.1.symm hP.2.2.1.symm hT1.2.2.1.symm hT2.2.2.1.symm]; exact h3
  · rw [g _ hB.2.2.2.1.symm hM.2.2.2.1.symm hP.2.2.2.1.symm hT1.2.2.2.1.symm hT2.2.2.2.1.symm]
    exact h4

section loop
variable {pl : Placement} {s0 : State} {C : Nat} {n : ℕ} {c1 c2 : BitVec 32}

/-- From `+0x88` with `w9 = op`: `multmodp(op, crc1) ^ crc2`, returned. -/
theorem cmb_fin (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded s0.mem)
    (hrun : s0.status = .Running) (hC : C = 2256 ∨ C = 2052) {r : BitVec 5 → BitVec 64}
    {ps : PState} {op : BitVec 32} (hop : regPoly op = X ^ (8 * n) % crc32P) (h9 : lo (r 9#5) = op)
    (h8 : lo (r 8#5) = POLY) (h0 : lo (r 0#5) = c1) (h1 : lo (r 1#5) = c2) (hk : Keep s0 r) :
    Reach pl s0 (CmbOk c1 c2 n) (mkS s0 (fA pl C + BitVec.ofNat 64 136) r ps) := by
  refine reach_exec hrun (c136 hP hCL hC) (ex_movw0 (by decide)) ?_
  rw [cstep]
  refine reach_exec hrun (c140 hP hCL hC) (ex_movz (by decide)) ?_
  rw [cstep]
  refine reach_exec hrun (c144 hP hCL hC) ex_b ?_
  rw [show fA pl C + BitVec.ofNat 64 (140 + 4) + 0x18#64 = fA pl C + BitVec.ofNat 64 148 + 20#64 by
    rw [cjump pl C (140 + 4) 0x18 168 (by decide), pc_add]]
  have hR : MMRegs 9#5 0#5 11#5 10#5 8#5 12#5 13#5 := by unfold MMRegs; decide
  refine mm_loop hrun (mmcode_c2 hP hCL hC) hR (a := op) (b := c1) ?hk ?hA ?hQ 31 0 _ _ rfl
    (exists_bit (ne_zero_of_regPoly hop)) (fun _ _ _ _ _ _ => rfl) ?hm ?hb ?hp
  case hA => simp [Function.update_apply, h9]
  case hQ => simp [Function.update_apply, h8]
  case hm => simp [Function.update_apply] <;> decide
  case hb => simp [Function.update_apply, h0]; rfl
  case hp => simp [Function.update_apply]; rfl
  case hk =>
    intro r' ps' hr' hP'
    rw [show fA pl C + BitVec.ofNat 64 148 + 44#64 = fA pl C + BitVec.ofNat 64 192 by rw [pc_add]]
    refine reach_exec hrun (c192 hP hCL hC) (ex_movw (by decide) (by decide)) ?_
    rw [cstep]
    refine reach_exec hrun (c196 hP hCL hC) (ex_eorx (by decide) (by decide) (by decide)) ?_
    rw [cstep]
    have e1 : r' 1#5 = r 1#5 := by
      rw [hr' 1#5 (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp [Function.update_apply]
    refine reach_ret hrun (c200 hP hCL hC) ?_ ⟨op, hop, ?_⟩
    · refine keep_update (keep_update ?_ (by decide) _) (by decide) _
      refine keep_of_agree5 ?_ (by decide) (by decide) (by decide) (by decide) (by decide) hr'
      exact keep_update (keep_update hk (by decide) _) (by decide) _
    · simp only [Function.update_self, Function.update_of_ne (show (0#5 : BitVec 5) ≠ 8#5 by decide),
        Function.update_of_ne (show (10#5 : BitVec 5) ≠ 8#5 by decide), e1, h1, hP', W_xor]

/-- From `+0x24` (after bit `i`), with `w9` the new accumulator: shift, bump `k`, exit or loop. -/
theorem cmb_tail (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded s0.mem)
    (hrun : s0.status = .Running) (hC : C = 2256 ∨ C = 2052) (hn : n < 2 ^ 63)
    {i : ℕ} {r : BitVec 5 → BitVec 64} {ps : PState} {pv : BitVec 32}
    (hq1 : 1 ≤ n / 2 ^ i) (h2 : r 2#5 = BitVec.ofNat 64 (n / 2 ^ i))
    (h10 : lo (r 10#5) = BitVec.ofNat 32 (3 + i)) (h9 : lo (r 9#5) = pv)
    (hpv : regPoly pv = X ^ (8 * (n % 2 ^ (i + 1))) % crc32P) (hI : CInv pl s0 c1 c2 r)
    (IH : 1 ≤ n / 2 ^ (i + 1) → ∀ r' ps', r' 2#5 = BitVec.ofNat 64 (n / 2 ^ (i + 1)) →
      lo (r' 10#5) = BitVec.ofNat 32 (3 + (i + 1)) → lo (r' 12#5) = pv → CInv pl s0 c1 c2 r' →
      Reach pl s0 (CmbOk c1 c2 n) (mkS s0 (fA pl C + BitVec.ofNat 64 60) r' ps')) :
    Reach pl s0 (CmbOk c1 c2 n) (mkS s0 (fA pl C + BitVec.ofNat 64 36) r ps) := by
  have hqlt : n / 2 ^ i < 2 ^ 63 := lt_of_le_of_lt (Nat.div_le_self _ _) hn
  refine reach_exec hrun (c36 hP hCL hC) (ex_asr1 (by decide) (by decide)) ?_
  rw [cstep]
  refine reach_exec hrun (c40 hP hCL hC) (ex_cmp1 (by decide)) ?_
  rw [cstep]
  refine reach_exec hrun (c44 hP hCL hC) (ex_add1 (by decide) (by decide)) ?_
  rw [cstep]
  refine reach_exec hrun (c48 hP hCL hC) (ex_movw (by decide) (by decide)) ?_
  rw [cstep]
  refine reach_exec hrun (c52 hP hCL hC) (ex_movx (by decide) (by decide)) ?_
  rw [cstep]
  refine reach_exec hrun (c56 hP hCL hC) ex_bcond ?_
  rw [Function.update_of_ne (show (2#5 : BitVec 5) ≠ 13#5 by decide), h2, ls_cmp1 _ hq1 (by omega)]
  have hdiv : n / 2 ^ i / 2 = n / 2 ^ (i + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
  have mk : ∀ v13 v10 v12 v2 : BitVec 64, CInv pl s0 c1 c2 (Function.update (Function.update
      (Function.update (Function.update r 13#5 v13) 10#5 v10) 12#5 v12) 2#5 v2) := fun v13 v10 v12 v2 =>
    cinv_update (cinv_update (cinv_update (cinv_update hI (d := 13#5) (by decide) v13)
      (d := 10#5) (by decide) v10) (d := 12#5) (by decide) v12) (d := 2#5) (by decide) v2
  by_cases hq : n / 2 ^ i = 1
  · simp only [hq, decide_true, if_true]
    rw [cjump pl C (52 + 4) 0x50 136 (by decide)]
    refine cmb_fin hP hCL hrun hC (op := pv) ?_ ?_ (mk _ _ _ _).2.1 (mk _ _ _ _).2.2.1
      (mk _ _ _ _).2.2.2.1 (mk _ _ _ _).2.2.2.2
    · rw [hpv]
      congr 3
      have h1 : n < 2 ^ (i + 1) := by
        rw [pow_succ]; have := Nat.div_add_mod n (2 ^ i); have := Nat.mod_lt n (show 0 < 2 ^ i by positivity)
        rw [hq] at *; nlinarith
      exact Nat.mod_eq_of_lt h1
    · simp [Function.update_apply, h9]
  · simp only [hq, decide_false, Bool.false_eq_true, if_false]
    rw [cstep]
    refine IH (by rw [← hdiv]; omega) _ _ ?_ ?_ ?_ (mk _ _ _ _)
    · simp [Function.update_apply, asr1_ofNat _ hqlt, hdiv]
    · simp only [Function.update_apply]; simp [h10, add1_ofNat32]; rfl
    · simp [Function.update_apply, h9]

/-- The loop head `+0x3c`, after `i` bits: `x2 = n >> i ≥ 1`, `w10 = 3 + i`, `w12 = x^(8 (n mod 2^i))`. -/
theorem cmb_head (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded s0.mem)
    (hrun : s0.status = .Running) (hC : C = 2256 ∨ C = 2052) (hn : n < 2 ^ 63)
    (htab : RoBytes s0.mem (pl.ρ "x2n_table [zlib_crc32]") zlibCrc32PlacedData2)
    (hT : ∀ k < 32, regPoly (word32 zlibCrc32PlacedData2 k) = pow2k crc32P k) :
    ∀ d i r ps pv, i + d = 62 → 1 ≤ n / 2 ^ i → r 2#5 = BitVec.ofNat 64 (n / 2 ^ i) →
      lo (r 10#5) = BitVec.ofNat 32 (3 + i) → lo (r 12#5) = pv →
      regPoly pv = X ^ (8 * (n % 2 ^ i)) % crc32P → CInv pl s0 c1 c2 r →
      Reach pl s0 (CmbOk c1 c2 n) (mkS s0 (fA pl C + BitVec.ofNat 64 60) r ps) := by
  intro d
  induction d with
  | zero =>
    intro i r ps pv hid hq1 h2 h10 h12 hpv hI
    exact cmb_body hP hCL hrun hC hn htab hT hq1 h2 h10 h12 hpv hI (fun h => by
      exfalso
      have : n / 2 ^ (i + 1) = 0 := by
        rw [Nat.div_eq_of_lt]; calc n < 2 ^ 63 := hn
          _ = 2 ^ (i + 1) := by congr 1; omega
      omega)
  | succ d ih =>
    intro i r ps pv hid hq1 h2 h10 h12 hpv hI
    exact cmb_body hP hCL hrun hC hn htab hT hq1 h2 h10 h12 hpv hI
      (fun hq1' r' ps' pv' h2' h10' h12' hpv' hI' =>
        ih (i + 1) r' ps' pv' (by omega) hq1' h2' h10' h12' hpv' hI')
where
  cmb_body (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded s0.mem)
      (hrun : s0.status = .Running) (hC : C = 2256 ∨ C = 2052) (hn : n < 2 ^ 63)
      (htab : RoBytes s0.mem (pl.ρ "x2n_table [zlib_crc32]") zlibCrc32PlacedData2)
      (hT : ∀ k < 32, regPoly (word32 zlibCrc32PlacedData2 k) = pow2k crc32P k)
      {i : ℕ} {r : BitVec 5 → BitVec 64} {ps : PState} {pv : BitVec 32}
      (hq1 : 1 ≤ n / 2 ^ i) (h2 : r 2#5 = BitVec.ofNat 64 (n / 2 ^ i))
      (h10 : lo (r 10#5) = BitVec.ofNat 32 (3 + i)) (h12 : lo (r 12#5) = pv)
      (hpv : regPoly pv = X ^ (8 * (n % 2 ^ i)) % crc32P) (hI : CInv pl s0 c1 c2 r)
      (IH : 1 ≤ n / 2 ^ (i + 1) → ∀ r' ps' pv', r' 2#5 = BitVec.ofNat 64 (n / 2 ^ (i + 1)) →
        lo (r' 10#5) = BitVec.ofNat 32 (3 + (i + 1)) → lo (r' 12#5) = pv' →
        regPoly pv' = X ^ (8 * (n % 2 ^ (i + 1))) % crc32P → CInv pl s0 c1 c2 r' →
        Reach pl s0 (CmbOk c1 c2 n) (mkS s0 (fA pl C + BitVec.ofNat 64 60) r' ps')) :
      Reach pl s0 (CmbOk c1 c2 n) (mkS s0 (fA pl C + BitVec.ofNat 64 60) r ps) := by
    have tail : ∀ (r' : BitVec 5 → BitVec 64) ps' (pv' : BitVec 32),
        regPoly pv' = X ^ (8 * (n % 2 ^ (i + 1))) % crc32P → r' 2#5 = r 2#5 → r' 10#5 = r 10#5 →
        lo (r' 9#5) = pv' → CInv pl s0 c1 c2 r' →
        Reach pl s0 (CmbOk c1 c2 n) (mkS s0 (fA pl C + BitVec.ofNat 64 36) r' ps') := by
      intro r' ps' pv' hpv' e2 e10 e9 hI'
      exact cmb_tail hP hCL hrun hC hn hq1 (by rw [e2, h2]) (by rw [e10, h10]) e9 hpv' hI'
        (fun hq1' r'' ps'' h2'' h10'' h12'' hI'' => IH hq1' r'' ps'' pv' h2'' h10'' h12'' hpv' hI'')
    obtain ⟨h11, h8, _, _, hk⟩ := hI
    refine reach_exec hrun (c60 hP hCL hC) (ex_tbz0 (by decide)) ?_
    rw [h2, getLsbD0_ofNat]
    by_cases hodd : n / 2 ^ i % 2 = 1
    · simp only [hodd, decide_true, Bool.true_eq_false, if_false]
      rw [cstep]
      refine reach_exec hrun (c64 hP hCL hC) (ex_and31 (by decide) (by decide)) ?_
      rw [cstep]
      refine reach_exec hrun (c68 hP hCL hC) (ex_movw0 (by decide)) ?_
      rw [cstep]
      refine reach_exec hrun (c72 hP hCL hC) (ex_movz (by decide)) ?_
      rw [cstep]
      have hidx : (3 + i) % 32 < 32 := Nat.mod_lt _ (by omega)
      have hld := read32_x2n htab _ hidx
      have haddr : ∀ v9 v14 : BitVec 64,
          (Function.update (Function.update (Function.update r 13#5 (W (lo (r 10#5) &&& 0x1f#32)))
            9#5 v9) 14#5 v14) 11#5 +
          W (lo ((Function.update (Function.update (Function.update r 13#5 (W (lo (r 10#5) &&& 0x1f#32)))
            9#5 v9) 14#5 v14) 13#5)) <<< 2 =
          pl.ρ "x2n_table [zlib_crc32]" + BitVec.ofNat 64 (4 * ((3 + i) % 32)) := by
        intro v9 v14
        simp only [Function.update_apply]
        simp only [show (11#5 : BitVec 5) = 14#5 ↔ False by decide,
          show (11#5 : BitVec 5) = 9#5 ↔ False by decide, show (11#5 : BitVec 5) = 13#5 ↔ False by decide,
          show (13#5 : BitVec 5) = 14#5 ↔ False by decide, show (13#5 : BitVec 5) = 9#5 ↔ False by decide,
          if_false, if_true, h11, h10, and31_ofNat32, idx_x2n _ hidx]
      refine reach_exec hrun (c76 hP hCL hC)
        (ex_ldrw (by decide) (by decide) (by decide) (by rw [haddr]; exact hld.1)) ?_
      rw [cstep]
      refine reach_exec hrun (c80 hP hCL hC) ex_b ?_
      rw [show fA pl C + BitVec.ofNat 64 (76 + 4) + 0x18#64 = fA pl C + BitVec.ofNat 64 84 + 20#64 by
        rw [cjump pl C (76 + 4) 0x18 104 (by decide), pc_add]]
      rw [haddr, hld.2]
      set a := word32 zlibCrc32PlacedData2 ((3 + i) % 32) with ha
      have hapoly : regPoly a = X ^ (2 ^ ((3 + i) % 32)) % crc32P := hT _ hidx
      have hR : MMRegs 13#5 12#5 14#5 9#5 8#5 15#5 16#5 := by unfold MMRegs; decide
      refine mm_loop hrun (mmcode_c1 hP hCL hC) hR (a := a) (b := pv) ?hk ?hA ?hQ 31 0 _ _ rfl
        (exists_bit (ne_zero_of_regPoly hapoly)) (fun _ _ _ _ _ _ => rfl) ?hm ?hb ?hp
      case hA => simp [Function.update_apply]
      case hQ => simp [Function.update_apply, h8]
      case hm => simp [Function.update_apply] <;> decide
      case hb => simp [Function.update_apply, h12]; rfl
      case hp => simp [Function.update_apply]; rfl
      case hk =>
        intro r' ps' hr' hP'
        rw [show fA pl C + BitVec.ofNat 64 84 + 44#64 = fA pl C + BitVec.ofNat 64 128 by rw [pc_add]]
        refine reach_exec hrun (c128 hP hCL hC) ex_b ?_
        rw [cjump pl C 128 0xffffffffffffffa4 36 (by decide)]
        refine tail r' ps' (pAcc a pv 32) (x2n_step n i a pv hapoly hpv hodd) ?_ ?_ ?_ ?_
        · rw [hr' 2#5 (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp [Function.update_apply]
        · rw [hr' 10#5 (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp [Function.update_apply]
        · rw [hP', lo_W]
        · refine cinv_agree ?_ (by intro j hj; rcases hj with rfl | rfl | rfl | rfl | rfl <;> decide) hr'
          exact cinv_update (cinv_update (cinv_update (cinv_update ⟨h11, h8, ‹_›, ‹_›, hk⟩
            (d := 13#5) (by decide) _) (d := 9#5) (by decide) _) (d := 14#5) (by decide) _)
            (d := 13#5) (by decide) _
    · simp only [show n / 2 ^ i % 2 = 0 by omega, show ¬ (0 = 1) by omega, decide_false, if_true]
      rw [cjump pl C 60 0xffffffffffffffe4 32 (by decide)]
      refine reach_exec hrun (c32 hP hCL hC) (ex_movw (by decide) (by decide)) ?_
      rw [cstep]
      refine tail _ ps pv (x2n_skip n i pv hpv (by omega)) ?_ ?_ ?_ ?_
      · simp [Function.update_apply]
      · simp [Function.update_apply]
      · simp [Function.update_apply, h12]
      · exact cinv_update ⟨h11, h8, ‹_›, ‹_›, hk⟩ (d := 9#5) (by decide) _

/-- From the entry. -/
theorem cmb_reach (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded s0.mem)
    (hrun : s0.status = .Running) (hC : C = 2256 ∨ C = 2052) (hn : n < 2 ^ 63)
    (htab : RoBytes s0.mem (pl.ρ "x2n_table [zlib_crc32]") zlibCrc32PlacedData2)
    (hT : ∀ k < 32, regPoly (word32 zlibCrc32PlacedData2 k) = pow2k crc32P k)
    (hpc : s0.pc = fA pl C) (h2 : s0.regs.regs 2#5 = BitVec.ofNat 64 n) :
    Reach pl s0 (CmbOk (lo (s0.regs.regs 0#5)) (lo (s0.regs.regs 1#5)) n) s0 := by
  apply reach_of_entry
  rw [hpc, show fA pl C = fA pl C + BitVec.ofNat 64 0 by simp]
  refine reach_exec hrun (c0 hP hCL hC) (ex_movz (by decide)) ?_
  rw [cstep]
  refine reach_exec hrun (c4 hP hCL hC) (ex_movk (by decide)) ?_
  rw [cstep]
  refine reach_exec hrun (c8 hP hCL hC) (ex_cbzx (by decide)) ?_
  simp only [Function.update_of_ne (show (2#5 : BitVec 5) ≠ 8#5 by decide), h2]
  have k2 : Keep s0 (Function.update (Function.update s0.regs.regs 8#5
      (W ((((0x8320#16 : BitVec 16).setWidth 64) <<< 0).setWidth 32))) 8#5
      (W ((((W (lo (Function.update s0.regs.regs 8#5
        (W ((((0x8320#16 : BitVec 16).setWidth 64) <<< 0).setWidth 32)) 8#5))) &&&
        ~~~(0xffff#64 <<< 16)) ||| ((0xedb8#16 : BitVec 16).setWidth 64 <<< 16)).setWidth 32))) :=
    keep_update (keep_update (keep_self s0) (by decide) _) (by decide) _
  by_cases hn0 : n = 0
  · subst hn0
    simp only [show BitVec.ofNat 64 0 = 0#64 from rfl, if_true]
    rw [cjump pl C 8 0x7c 132 (by decide)]
    refine reach_exec hrun (c132 hP hCL hC) (ex_movz (by decide)) ?_
    rw [cstep]
    refine cmb_fin hP hCL hrun hC (op := 0x80000000#32) ?_ ?_ ?_ ?_ ?_ (keep_update k2 (by decide) _)
    · rw [regPoly_one, mul_zero, pow_zero, one_mod]
    · simp [Function.update_apply] <;> decide
    · simp [Function.update_apply] <;> decide
    · simp [Function.update_apply]
    · simp [Function.update_apply]
  · have hne : BitVec.ofNat 64 n ≠ 0#64 := by
      intro h; have := congrArg BitVec.toNat h; rw [toNat_ofNat_lt n (by omega)] at this; simp at this
      exact hn0 this
    simp only [hne, if_false]
    rw [cstep]
    refine reach_exec hrun (c12 hP hCL hC) (ex_movz (by decide)) ?_
    rw [cstep]
    refine reach_exec hrun (c16 hP hCL hC) (ex_movz (by decide)) ?_
    rw [cstep, fA_add]
    refine reach_steps (steps_pairCmb hP hCL hrun (C + (16 + 4))
      (by rcases hC with rfl | rfl <;> simp)) ?_
    rw [show pl.base + BitVec.ofNat 64 (C + (16 + 4) + 8) = fA pl C + BitVec.ofNat 64 28 by
      rw [fA_add]]
    refine reach_exec hrun (c28 hP hCL hC) ex_b ?_
    rw [cjump pl C 28 0x20 60 (by decide)]
    refine cmb_head hP hCL hrun hC hn htab hT 62 0 _ _ 0x80000000#32 rfl (by simp; omega) ?_ ?_ ?_ ?_ ?_
    · simp [Function.update_apply, h2]
    · simp [Function.update_apply] <;> decide
    · simp [Function.update_apply] <;> decide
    · rw [regPoly_one, pow_zero, Nat.mod_one, mul_zero, pow_zero, one_mod]
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [Function.update_apply]
      · simp [Function.update_apply] <;> decide
      · simp [Function.update_apply]
      · simp [Function.update_apply]
      · exact keep_update (keep_update (keep_update k2 (by decide) _) (by decide) _) (by decide) _

end loop

theorem rd_s0 (s0 : State) (k : BitVec 5) (hk : k ≠ 31#5) : s0.readReg64 (.gpr k) = s0.regs.regs k := by
  simp [State.readReg64, RegFile.read, hk]

theorem combine_one (hT : ∀ k < 32, regPoly (word32 zlibCrc32PlacedData2 k) = pow2k crc32P k)
    (hKJ : CrcAppendOfCrcs) (name : String) (C : Nat) (hC : C = 2256 ∨ C = 2052)
    (hex : name ∈ zlibCrc32Lib.exports) (hfn : ∀ pl, zlibCrc32Lib.fnAddr pl name = fA pl C) :
    zlibCrc32Lib.subroutineOk name crc32CombineSpec := by
  refine ⟨hex, ?_⟩
  intro pl hP g R s0 hpc hrun hpre hal hCL
  change (prog pl).CodeLoaded s0.mem at hCL
  rw [hfn] at hpc
  obtain ⟨h1, h2, h3⟩ := sat_pure hpre
  obtain ⟨hx2, hn⟩ := ofNat_of_toInt h3
  rw [show Reg.x0 = Reg.gpr 0#5 from rfl, rd_s0 s0 _ (by decide)] at h1
  rw [show Reg.x1 = Reg.gpr 1#5 from rfl, rd_s0 s0 _ (by decide)] at h2
  have h2' : s0.regs.regs 2#5 = BitVec.ofNat 64 g.2.length := by
    rw [← rd_s0 s0 _ (by decide)]; exact hx2
  refine outcome_of_reach hrun (cmb_reach hP hCL hrun hC hn (x2n_ro hpre) hT hpc h2')
    (fun r ps hX _ => sat_pure_swap hpre (fun _ => ?_))
  obtain ⟨op, hop, hx⟩ := hX
  show Holds32 (r 0#5) _
  rw [hx]
  exact holds32_W _ _ (combine_math hKJ g.1 g.2 _ _ _ h1 h2 hop)

theorem combine_ok (hT : ∀ k < 32, regPoly (word32 zlibCrc32PlacedData2 k) = pow2k crc32P k)
    (hKJ : CrcAppendOfCrcs) :
    zlibCrc32Lib.subroutineOk "crc32_combine" crc32CombineSpec ∧
      zlibCrc32Lib.subroutineOk "crc32_combine64" crc32CombineSpec :=
  ⟨combine_one hT hKJ _ 2256 (Or.inl rfl) (by decide) (fun _ => rfl),
    combine_one hT hKJ _ 2052 (Or.inr rfl) (by decide) (fun _ => rfl)⟩

end ZlibCrc32.Small
end

open ZlibCrc32 in
theorem solution :
    zlibCrc32Lib.subroutineOk "crc32_combine" crc32CombineSpec ∧
      zlibCrc32Lib.subroutineOk "crc32_combine64" crc32CombineSpec :=
  ZlibCrc32.Small.combine_ok crc_tables_eq.2.2.2 (fun P u hP hu M₁ M₂ v v₁ v₂ =>
    KadatchJenkins.crc_append_of_crcs P u hP hu M₁ M₂ v v₁ v₂)
