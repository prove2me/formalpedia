-- Prove2me | solution 1 for ZlibCrc32.subroutineOk_crc32_combine_op
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T11:01:36.574798+00:00
-- url     : https://prove2.me/submissions/ff90adf2-14d9-4064-b3c5-a11741be210e

import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases
import Definitions.Def_ZlibCrc32_Spec
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

theorem ex_b {off : BitVec 64} :
    execInstWithSvc svc (.b off) (mkS s0 pc r ps) = mkS s0 (pc + off) r ps := rfl

theorem ex_bcond {c : CondCode} {off : BitVec 64} :
    execInstWithSvc svc (.bCond c off) (mkS s0 pc r ps) =
      if ConditionHolds c ps then mkS s0 (pc + off) r ps else mkS s0 (pc + 4#64) r ps := rfl

theorem ex_ret :
    execInstWithSvc svc (.ret (.gpr 30#5)) (mkS s0 pc r ps) = mkS s0 (r 30#5) r ps := by
  show State.setPC _ _ = _
  simp [rd_gpr]

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

/-- Returned with `x0 = X` and the registers from `x19` up untouched. -/
def Fin (s0 : State) (X : BitVec 64) (sf : State) : Prop :=
  ∃ r ps, sf = mkS s0 (s0.regs.regs 30#5) r ps ∧ r 0#5 = X ∧ Keep s0 r

def Reach (pl : Placement) (s0 : State) (X : BitVec 64) (s : State) : Prop :=
  ∃ sf, Steps (prog pl) s sf ∧ Fin s0 X sf

theorem reach_step {pl : Placement} {s0 s s' : State} {X : BitVec 64} (h : Step (prog pl) s s')
    (h' : Reach pl s0 X s') : Reach pl s0 X s := by
  obtain ⟨sf, h1, h2⟩ := h'
  exact ⟨sf, Steps.step h h1, h2⟩

theorem reach_exec {pl : Placement} {s0 : State} {X pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {ps : PState} {inst : Instr} {s' : State} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem s0.mem pc = some inst)
    (he : execInstWithSvc (evalSvc Syscall.standard) inst (mkS s0 pc r ps) = s')
    (h : Reach pl s0 X s') : Reach pl s0 X (mkS s0 pc r ps) := by
  rw [← he] at h
  exact reach_step (step_mkS hrun hf) h

theorem reach_ret {pl : Placement} {s0 : State} {pc : BitVec 64} {r : BitVec 5 → BitVec 64}
    {ps : PState} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem s0.mem pc = some (.ret (.gpr 30#5))) (hk : Keep s0 r) :
    Reach pl s0 (r 0#5) (mkS s0 pc r ps) := by
  refine reach_exec hrun hf ex_ret ⟨_, Steps.refl _, r, ps, ?_, rfl, hk⟩
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
variable {pl : Placement} {s0 : State} {X : BitVec 64} {L : BitVec 64}
  {A B M P Q T1 T2 : BitVec 5}

/-- The body `L .. L+0x10`: `b := b·x mod p`, `m := m >> 1`. -/
theorem mm_body (hrun : s0.status = .Running) (hc : MMCode pl s0.mem L A B M P Q T1 T2)
    (hR : MMRegs A B M P Q T1 T2) {r : BitVec 5 → BitVec 64} {ps : PState}
    (hQ : lo (r Q) = POLY)
    (h : ∀ ps', Reach pl s0 X (mkS s0 (L + 20#64)
      (Function.update (Function.update (Function.update (Function.update r T1 (W (lo (r B) >>> 1)))
        M (W (lo (r M) >>> 1))) T2 (W ((lo (r B) >>> 1) ^^^ POLY))) B (W (mulx (lo (r B))))) ps')) :
    Reach pl s0 X (mkS s0 L r ps) := by
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
      r' P = W (pAcc a b 32) → Reach pl s0 X (mkS s0 (L + 44#64) r' ps'))
    (hA0 : lo (r0 A) = a) (hQ0 : lo (r0 Q) = POLY)
    {j : ℕ} (hj : j < 32) {r : BitVec 5 → BitVec 64} {ps : PState}
    (hex : ∃ k, j ≤ k ∧ k < 32 ∧ a.getLsbD (31 - k) = true)
    (hr : ∀ i, i ≠ B → i ≠ M → i ≠ P → i ≠ T1 → i ≠ T2 → r i = r0 i)
    (hm : lo (r M) = 0x80000000#32 >>> j) (hb : lo (r B) = mulxN j b) (hp : lo (r P) = pAcc a b j)
    (IH : j + 1 < 32 → ∀ r' ps', (∃ k, j + 1 ≤ k ∧ k < 32 ∧ a.getLsbD (31 - k) = true) →
      (∀ i, i ≠ B → i ≠ M → i ≠ P → i ≠ T1 → i ≠ T2 → r' i = r0 i) →
      lo (r' M) = 0x80000000#32 >>> (j + 1) → lo (r' B) = mulxN (j + 1) b →
      lo (r' P) = pAcc a b (j + 1) → Reach pl s0 X (mkS s0 (L + 20#64) r' ps')) :
    Reach pl s0 X (mkS s0 (L + 20#64) r ps) := by
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
      r' P = W (pAcc a b 32) → Reach pl s0 X (mkS s0 (L + 44#64) r' ps'))
    (hA0 : lo (r0 A) = a) (hQ0 : lo (r0 Q) = POLY) :
    ∀ d j r ps, j + d = 31 → (∃ k, j ≤ k ∧ k < 32 ∧ a.getLsbD (31 - k) = true) →
      (∀ i, i ≠ B → i ≠ M → i ≠ P → i ≠ T1 → i ≠ T2 → r i = r0 i) →
      lo (r M) = 0x80000000#32 >>> j → lo (r B) = mulxN j b → lo (r P) = pAcc a b j →
      Reach pl s0 X (mkS s0 (L + 20#64) r ps) := by
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
    {s0 : State} {X : BitVec 64} (hrun : s0.status = .Running) (h : Reach pl s0 X s0)
    (hpost : ∀ r ps, r 0#5 = X → Keep s0 r →
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

theorem reach_of_entry {pl : Placement} {s0 : State} {X : BitVec 64}
    (h : Reach pl s0 X (mkS s0 s0.pc s0.regs.regs s0.pstate)) : Reach pl s0 X s0 := by
  rwa [mkS_self] at h

theorem reach_ret' {pl : Placement} {s0 : State} {pc X : BitVec 64} {r : BitVec 5 → BitVec 64}
    {ps : PState} (hrun : s0.status = .Running)
    (hf : (prog pl).fetchMem s0.mem pc = some (.ret (.gpr 30#5))) (hk : Keep s0 r) (hX : r 0#5 = X) :
    Reach pl s0 X (mkS s0 pc r ps) := by
  rw [← hX]; exact reach_ret hrun hf hk

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
/-! # `crc32_combine_op(crc1, crc2, op) = multmodp(op, crc1) ^ crc2`

```
0xabc  mov  w10, #0x8320        0xad0  .. 0xae4  the multmodp loop (a = w2, b = w0, m = w9,
0xac0  mov  w8, wzr                              p = w8, POLY = w10, temps w11, w12)
0xac4  mov  w9, #0x80000000     0xafc  mov  w9, w1
0xac8  movk w10, #0xedb8, lsl 16  0xb00  eor  x0, x9, x8
0xacc  b    0xae4               0xb04  ret
``` -/

namespace ZlibCrc32.Small

set_option maxRecDepth 100000

open Arm64 Arm64.Obj

theorem fnAddr_combine_op (pl : Placement) :
    zlibCrc32Lib.fnAddr pl "crc32_combine_op" = pl.base + BitVec.ofNat 64 2748 := rfl

section
variable {pl : Placement} {m : Memory} (hP : zlibCrc32Lib.Placeable pl) (hCL : (prog pl).CodeLoaded m)
include hP hCL

theorem mmcode_op : MMCode pl m (pl.base + BitVec.ofNat 64 2768) 2#5 0#5 9#5 8#5 10#5 11#5 12#5 where
  f0 := fetch_plain hP hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  f1 := fetch_off hP hCL 2768 4 (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  f2 := fetch_off hP hCL 2768 8 (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  f3 := fetch_off hP hCL 2768 12 (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  f4 := fetch_off hP hCL 2768 16 (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  f5 := fetch_off hP hCL 2768 20 (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  f6 := fetch_off hP hCL 2768 24 (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  f7 := fetch_off hP hCL 2768 28 (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  f8 := fetch_off hP hCL 2768 32 (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  f9 := fetch_off hP hCL 2768 36 (by decide) (by decide) (by decide +kernel) (by decide +kernel)
  f10 := fetch_off hP hCL 2768 40 (by decide) (by decide) (by decide +kernel) (by decide +kernel)

theorem fop_0 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 2748) =
    some (.moveWide .W32 .MOVZ (.gpr 10#5) 0x8320#16 0) :=
  fetch_plain hP hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem fop_4 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 2752) =
    some (.logicalShift .W32 .ORR (.gpr 8#5) .xzr .xzr .LSL 0) :=
  fetch_plain hP hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem fop_8 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 2756) =
    some (.moveWide .W32 .MOVZ (.gpr 9#5) 0x8000#16 16) :=
  fetch_plain hP hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem fop_12 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 2760) =
    some (.moveWide .W32 .MOVK (.gpr 10#5) 0xedb8#16 16) :=
  fetch_plain hP hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem fop_16 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 2764) = some (.b 0x18#64) :=
  fetch_plain hP hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem fop_64 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 2812) =
    some (.logicalShift .W32 .ORR (.gpr 9#5) .xzr (.gpr 1#5) .LSL 0) :=
  fetch_plain hP hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem fop_68 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 2816) =
    some (.logicalShift .W64 .EOR (.gpr 0#5) (.gpr 9#5) (.gpr 8#5) .LSL 0) :=
  fetch_plain hP hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)
theorem fop_72 : (prog pl).fetchMem m (pl.base + BitVec.ofNat 64 2820) = some (.ret (.gpr 30#5)) :=
  fetch_plain hP hCL (by decide) (by decide) (by decide +kernel) (by decide +kernel)

end

theorem M0_lit : lo (W ((((0x8000#16 : BitVec 16).setWidth 64) <<< 16).setWidth 32)) =
    (0x80000000#32 : BitVec 32) >>> 0 := by decide

/-- The machine part: from the entry, the run returns with `x0 = crc2 ^ multmodp(op, crc1)`. -/
theorem combine_op_reach {pl : Placement} {s0 : State} (hP : zlibCrc32Lib.Placeable pl)
    (hCL : (prog pl).CodeLoaded s0.mem) (hrun : s0.status = .Running)
    (hpc : s0.pc = pl.base + BitVec.ofNat 64 2748) (ha : lo (s0.regs.regs 2#5) ≠ 0#32) :
    Reach pl s0 (W (lo (s0.regs.regs 1#5) ^^^ pAcc (lo (s0.regs.regs 2#5)) (lo (s0.regs.regs 0#5)) 32)) s0 := by
  apply reach_of_entry
  rw [hpc]
  set r0 := s0.regs.regs with hr0
  refine reach_exec hrun (fop_0 hP hCL) (ex_movz (by decide)) ?_
  rw [pc_add]
  refine reach_exec hrun (fop_4 hP hCL) (ex_movw0 (by decide)) ?_
  rw [pc_add]
  refine reach_exec hrun (fop_8 hP hCL) (ex_movz (by decide)) ?_
  rw [pc_add]
  refine reach_exec hrun (fop_12 hP hCL) (ex_movk (by decide)) ?_
  rw [pc_add]
  refine reach_exec hrun (fop_16 hP hCL) ex_b ?_
  rw [show pl.base + BitVec.ofNat 64 (2760 + 4) + 0x18#64 = pl.base + BitVec.ofNat 64 2768 + 20#64 by
    rw [BitVec.add_assoc, BitVec.add_assoc]; rfl]
  have hR : MMRegs 2#5 0#5 9#5 8#5 10#5 11#5 12#5 := by unfold MMRegs; decide
  refine mm_loop hrun (mmcode_op hP hCL) hR (a := lo (r0 2#5)) (b := lo (r0 0#5)) ?hk ?hA ?hQ 31 0 _ _
    rfl (exists_bit ha) (fun _ _ _ _ _ _ => rfl) ?hm ?hb ?hp
  case hA => simp [Function.update_apply]
  case hQ => simp [Function.update_apply]; decide
  case hm => simp only [Function.update_apply]; exact M0_lit
  case hb => simp [Function.update_apply]; rfl
  case hp => simp [Function.update_apply]; rfl
  case hk =>
    intro r' ps' hr' hP'
    rw [show pl.base + BitVec.ofNat 64 2768 + 44#64 = pl.base + BitVec.ofNat 64 2812 by
      rw [BitVec.add_assoc]; rfl]
    refine reach_exec hrun (fop_64 hP hCL) (ex_movw (by decide) (by decide)) ?_
    rw [pc_add]
    refine reach_exec hrun (fop_68 hP hCL) (ex_eorx (by decide) (by decide) (by decide)) ?_
    rw [pc_add]
    have h1 : r' 1#5 = r0 1#5 := by
      rw [hr' 1#5 (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp [Function.update_apply]
    refine reach_ret' hrun (fop_72 hP hCL) ?_ ?_
    · refine keep_update (keep_update ?_ (by decide) _) (by decide) _
      refine keep_of_agree5 ?_ (by decide) (by decide) (by decide) (by decide) (by decide) hr'
      exact keep_update (keep_update (keep_update (keep_update (keep_self s0) (by decide) _)
        (by decide) _) (by decide) _) (by decide) _
    · simp only [Function.update_self, Function.update_of_ne (show (0#5 : BitVec 5) ≠ 9#5 by decide),
        Function.update_of_ne (show (8#5 : BitVec 5) ≠ 9#5 by decide), h1, hP', W_xor]

/-- `crc32_combine_op` meets its contract, given Kadatch–Jenkins' concatenation theorem. -/
theorem combine_op_ok (hKJ : CrcAppendOfCrcs) :
    zlibCrc32Lib.subroutineOk "crc32_combine_op" crc32CombineOpSpec := by
  refine ⟨by decide, ?_⟩
  intro pl hP g R s0 hpc hrun hpre hal hCL
  change (prog pl).CodeLoaded s0.mem at hCL
  rw [fnAddr_combine_op] at hpc
  obtain ⟨h1, h2, hop⟩ := sat_pure hpre
  have ha : lo (s0.regs.regs 2#5) ≠ 0#32 := ne_zero_of_regPoly hop
  refine outcome_of_reach hrun (combine_op_reach hP hCL hrun hpc ha) (fun r ps hX _ => ?_)
  refine sat_pure_swap hpre (fun _ => ?_)
  show Holds32 (r 0#5) _
  rw [hX]
  exact holds32_W _ _ (combine_math hKJ g.1 g.2 _ _ _ h1 h2 hop)

end ZlibCrc32.Small
end

open ZlibCrc32 in
theorem solution : zlibCrc32Lib.subroutineOk "crc32_combine_op" crc32CombineOpSpec :=
  ZlibCrc32.Small.combine_op_ok (fun P u hP hu M₁ M₂ v v₁ v₂ =>
    KadatchJenkins.crc_append_of_crcs P u hP hu M₁ M₂ v v₁ v₂)
