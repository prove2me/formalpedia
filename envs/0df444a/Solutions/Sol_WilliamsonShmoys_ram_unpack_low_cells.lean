-- Prove2me | solution 1 for WilliamsonShmoys.ram_unpack_low_cells
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T15:24:52.216941+00:00
-- url     : https://prove2.me/submissions/950abb94-2d0f-4c81-8a10-a9d956d2b929

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false

namespace HV
open WilliamsonShmoys PlanarRAMInstruction

lemma step_exec (p : List PlanarRAMInstruction) (s : PlanarRAMState) (ins : PlanarRAMInstruction)
    (h : p[s.pc]? = some ins) : planarRAMStep p s = execInstr ins s := by
  unfold planarRAMStep
  rw [h]
  cases ins <;> rfl

lemma run_add (p : List PlanarRAMInstruction) (s : PlanarRAMState) (a b : ℕ) :
    planarRAMRun p s (a + b) = planarRAMRun p (planarRAMRun p s a) b := by
  unfold planarRAMRun
  rw [add_comm, Function.iterate_add_apply]

lemma run_succ (p : List PlanarRAMInstruction) (s : PlanarRAMState) (t : ℕ) :
    planarRAMRun p s (t + 1) = planarRAMRun p (planarRAMStep p s) t := by
  unfold planarRAMRun
  rw [Function.iterate_succ_apply]

lemma run_zero (p : List PlanarRAMInstruction) (s : PlanarRAMState) :
    planarRAMRun p s 0 = s := rfl

section
variable (p : List PlanarRAMInstruction) (base : ℕ)
  (hcode : CodeAt p base
    [natConst 9 0, natBranch 10 8 (base + 2) (base + 5), natSub 8 8 10, natAdd 9 9 11, jump (base + 1)])
include hcode

lemma code_at (i : ℕ) (hi : i < 5) :
    p[base + i]? = ([natConst 9 0, natBranch 10 8 (base + 2) (base + 5), natSub 8 8 10,
      natAdd 9 9 11, jump (base + 1)] : List PlanarRAMInstruction)[i]? :=
  hcode i (by simpa using hi)

lemma halve_loop :
    ∀ (x q : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), M 8 = x → M 9 = q → M 10 = 2 → M 11 = 1 →
      (planarRAMRun p ⟨base + 1, M, R⟩ (4 * (x / 2) + 1)).pc = base + 5 ∧
      (planarRAMRun p ⟨base + 1, M, R⟩ (4 * (x / 2) + 1)).natMem 8 = x % 2 ∧
      (planarRAMRun p ⟨base + 1, M, R⟩ (4 * (x / 2) + 1)).natMem 9 = q + x / 2 ∧
      (∀ a, a ≠ 8 → a ≠ 9 → (planarRAMRun p ⟨base + 1, M, R⟩ (4 * (x / 2) + 1)).natMem a = M a) ∧
      (planarRAMRun p ⟨base + 1, M, R⟩ (4 * (x / 2) + 1)).realMem = R := by
  intro x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    intro q M R h8 h9 h10 h11
    have hb : p[base + 1]? = some (natBranch 10 8 (base + 2) (base + 5)) := by
      simpa using code_at p base hcode 1 (by norm_num)
    by_cases hx : x < 2
    · have hq : x / 2 = 0 := by omega
      have hle : ¬ M 10 ≤ M 8 := by omega
      rw [hq, show 4 * 0 + 1 = 0 + 1 from rfl, run_succ, run_zero, step_exec p _ _ hb]
      simp only [execInstr, if_neg hle]
      refine ⟨trivial, ?_, ?_, fun a _ _ => trivial, trivial⟩
      · show M 8 = x % 2; rw [h8]; omega
      · show M 9 = q + 0; rw [h9]; rfl
    · have i2 : p[base + 2]? = some (natSub 8 8 10) := by simpa using code_at p base hcode 2 (by norm_num)
      have i3 : p[base + 3]? = some (natAdd 9 9 11) := by simpa using code_at p base hcode 3 (by norm_num)
      have i4 : p[base + 4]? = some (jump (base + 1)) := by simpa using code_at p base hcode 4 (by norm_num)
      have hle : M 10 ≤ M 8 := by omega
      have e : planarRAMRun p ⟨base + 1, M, R⟩ 4 =
          ⟨base + 1, Function.update (Function.update M 8 (x - 2)) 9 (q + 1), R⟩ := by
        rw [show planarRAMRun p ⟨base + 1, M, R⟩ 4 =
            planarRAMRun p ⟨base + 1, M, R⟩ (0 + 1 + 1 + 1 + 1) from rfl, run_succ,
          step_exec p _ _ hb]
        simp only [execInstr, if_pos hle]
        rw [run_succ, step_exec p _ _ i2, run_succ]
        simp only [execInstr]
        rw [step_exec p _ _ (by simpa using i3), run_succ]
        simp only [execInstr]
        rw [step_exec p _ _ (by simpa using i4), run_zero]
        simp only [execInstr, h8, h10, h11, Function.update_of_ne (show (9:ℕ) ≠ 8 by norm_num),
          Function.update_of_ne (show (11:ℕ) ≠ 8 by norm_num), h9]
      have hsplit : 4 * (x / 2) + 1 = 4 + (4 * ((x - 2) / 2) + 1) := by omega
      rw [hsplit, run_add, e]
      set M' := Function.update (Function.update M 8 (x - 2)) 9 (q + 1) with hM'
      have hfr : ∀ a, a ≠ 8 → a ≠ 9 → M' a = M a := by
        intro a a8 a9; rw [hM', Function.update_of_ne a9, Function.update_of_ne a8]
      obtain ⟨r1, r2, r3, r4, r5⟩ := ih (x - 2) (by omega) (q + 1) M' R
        (by rw [hM', Function.update_of_ne (by norm_num), Function.update_self])
        (by rw [hM', Function.update_self])
        (by rw [hfr 10 (by norm_num) (by norm_num), h10])
        (by rw [hfr 11 (by norm_num) (by norm_num), h11])
      refine ⟨r1, by rw [r2]; omega, by rw [r3]; omega,
        fun a a8 a9 => (r4 a a8 a9).trans (hfr a a8 a9), r5⟩

theorem halve_fragment (s : PlanarRAMState) (hpc : s.pc = base) (h10 : s.natMem 10 = 2)
    (h11 : s.natMem 11 = 1) :
    let x := s.natMem 8
    let s' := planarRAMRun p s (4 * (x / 2) + 2)
    s'.pc = base + 5 ∧ s'.natMem 8 = x % 2 ∧ s'.natMem 9 = x / 2 ∧
      (∀ a, a ≠ 8 → a ≠ 9 → s'.natMem a = s.natMem a) ∧ s'.realMem = s.realMem := by
  intro x
  have c0 : p[base + 0]? = some (natConst 9 0) := by simpa using code_at p base hcode 0 (by norm_num)
  have e : planarRAMRun p s 1 = ⟨base + 1, Function.update s.natMem 9 0, s.realMem⟩ := by
    rw [show planarRAMRun p s 1 = planarRAMRun p s (0 + 1) from rfl, run_succ, run_zero,
      step_exec p _ _ (by rw [hpc]; simpa using c0)]
    simp only [execInstr, hpc]
  rw [show 4 * (x / 2) + 2 = 1 + (4 * (x / 2) + 1) by ring, run_add, e]
  have hfr : ∀ a, a ≠ 9 → Function.update s.natMem 9 0 a = s.natMem a :=
    fun a a9 => Function.update_of_ne a9 _ _
  obtain ⟨r1, r2, r3, r4, r5⟩ := halve_loop p base hcode x 0 (Function.update s.natMem 9 0) s.realMem
    (by rw [hfr 8 (by norm_num)]) (by simp)
    (by rw [hfr 10 (by norm_num), h10]) (by rw [hfr 11 (by norm_num), h11])
  refine ⟨r1, r2, by rw [r3]; simp, fun a a8 a9 => (r4 a a8 a9).trans (hfr a a9), r5⟩

end

lemma codeAt_sub (p : List PlanarRAMInstruction) (base off : ℕ) (code sub : List PlanarRAMInstruction)
    (hcode : CodeAt p base code) (hsub : ∀ i, i < sub.length → code[off + i]? = sub[i]?) :
    CodeAt p (base + off) sub := by
  intro i hi
  have h := hsub i hi
  have hlen : off + i < code.length := by
    by_contra hc
    push_neg at hc
    rw [List.getElem?_eq_none hc] at h
    exact absurd h.symm (by simp [List.getElem?_eq_getElem hi])
  rw [add_assoc, hcode (off + i) hlen, h]

lemma arith_unpack (k b2 b3 b4 b5 b6 b7 : ℕ)
    (h2 : b2 ≤ 1) (h3 : b3 ≤ 1) (h4 : b4 ≤ 1) (h5 : b5 ≤ 1) (h6 : b6 ≤ 1) (h7 : b7 ≤ 1) :
    (64 * k + 32 * b2 + 16 * b3 + 8 * b4 + 4 * b5 + 2 * b6 + b7) / 64 = k ∧
      (64 * k + 32 * b2 + 16 * b3 + 8 * b4 + 4 * b5 + 2 * b6 + b7) % 2 = b7 ∧
      (64 * k + 32 * b2 + 16 * b3 + 8 * b4 + 4 * b5 + 2 * b6 + b7) / 2 % 2 = b6 ∧
      (64 * k + 32 * b2 + 16 * b3 + 8 * b4 + 4 * b5 + 2 * b6 + b7) / 4 % 2 = b5 ∧
      (64 * k + 32 * b2 + 16 * b3 + 8 * b4 + 4 * b5 + 2 * b6 + b7) / 8 % 2 = b4 ∧
      (64 * k + 32 * b2 + 16 * b3 + 8 * b4 + 4 * b5 + 2 * b6 + b7) / 16 % 2 = b3 ∧
      (64 * k + 32 * b2 + 16 * b3 + 8 * b4 + 4 * b5 + 2 * b6 + b7) / 32 % 2 = b2 := by
  omega

lemma run_succ_right (p : List PlanarRAMInstruction) (s : PlanarRAMState) (t : ℕ) :
    planarRAMRun p s (t + 1) = planarRAMStep p (planarRAMRun p s t) := by
  unfold planarRAMRun
  rw [Function.iterate_succ_apply']

section
variable (p : List PlanarRAMInstruction) (base : ℕ)
  (hcode : CodeAt p base
    [natConst 10 2,
      natConst 11 1,
      natConst 12 0,
      natAdd 32 0 12,
      natAdd 8 1 12,
      natConst 9 0,
      natBranch 10 8 (base + 7) (base + 10),
      natSub 8 8 10,
      natAdd 9 9 11,
      jump (base + 6),
      natAdd 46 8 12,
      natAdd 8 9 12,
      natConst 9 0,
      natBranch 10 8 (base + 14) (base + 17),
      natSub 8 8 10,
      natAdd 9 9 11,
      jump (base + 13),
      natAdd 44 8 12,
      natAdd 8 9 12,
      natConst 9 0,
      natBranch 10 8 (base + 21) (base + 24),
      natSub 8 8 10,
      natAdd 9 9 11,
      jump (base + 20),
      natAdd 42 8 12,
      natAdd 8 9 12,
      natConst 9 0,
      natBranch 10 8 (base + 28) (base + 31),
      natSub 8 8 10,
      natAdd 9 9 11,
      jump (base + 27),
      natAdd 40 8 12,
      natAdd 8 9 12,
      natConst 9 0,
      natBranch 10 8 (base + 35) (base + 38),
      natSub 8 8 10,
      natAdd 9 9 11,
      jump (base + 34),
      natAdd 38 8 12,
      natAdd 8 9 12,
      natConst 9 0,
      natBranch 10 8 (base + 42) (base + 45),
      natSub 8 8 10,
      natAdd 9 9 11,
      jump (base + 41),
      natAdd 36 8 12,
      natAdd 8 9 12,
      natAdd 34 8 12])
include hcode

/-- Round `j` (`j < 6`): halve cell 8, store the remainder at `46 - 2*j`, move the quotient to 8. -/
lemma round_step (j : ℕ) (hj : j < 6) (M : ℕ → ℕ) (R : ℕ → ℝ) (h10 : M 10 = 2) (h11 : M 11 = 1)
    (h12 : M 12 = 0) :
    let x := M 8
    let s' := planarRAMRun p ⟨base + (5 + 7 * j), M, R⟩ (4 * (x / 2) + 4)
    s'.pc = base + (5 + 7 * (j + 1)) ∧ s'.natMem 8 = x / 2 ∧ s'.natMem (46 - 2 * j) = x % 2 ∧
      (∀ a, a ≠ 8 → a ≠ 9 → a ≠ 46 - 2 * j → s'.natMem a = M a) ∧ s'.realMem = R := by
  intro x
  have hH : CodeAt p (base + (5 + 7 * j))
      [natConst 9 0, natBranch 10 8 (base + (5 + 7 * j) + 2) (base + (5 + 7 * j) + 5), natSub 8 8 10,
        natAdd 9 9 11, jump (base + (5 + 7 * j) + 1)] := by
    apply codeAt_sub p base _ _ _ hcode
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases j <;> interval_cases i <;> simp <;> ring_nf
  have hA : p[base + (5 + 7 * j) + 5]? = some (natAdd (46 - 2 * j) 8 12) := by
    have := hcode (5 + 7 * j + 5) (by simp; omega)
    rw [← add_assoc] at this
    rw [this]
    interval_cases j <;> simp
  have hB : p[base + (5 + 7 * j) + 6]? = some (natAdd 8 9 12) := by
    have := hcode (5 + 7 * j + 6) (by simp; omega)
    rw [← add_assoc] at this
    rw [this]
    interval_cases j <;> simp
  obtain ⟨r1, r2, r3, r4, r5⟩ := halve_fragment p (base + (5 + 7 * j)) hH ⟨base + (5 + 7 * j), M, R⟩
    rfl h10 h11
  rw [show 4 * (x / 2) + 4 = (4 * (x / 2) + 2) + 1 + 1 by ring, run_succ_right, run_succ_right]
  set s1 := planarRAMRun p ⟨base + (5 + 7 * j), M, R⟩ (4 * (M 8 / 2) + 2) with hs1
  have ht : 46 - 2 * j ≠ 8 := by omega
  have ht9 : 46 - 2 * j ≠ 9 := by omega
  have ht12 : 46 - 2 * j ≠ 12 := by omega
  rw [step_exec p s1 _ (by rw [r1]; exact hA)]
  rw [step_exec p _ _ (by simp only [execInstr, r1]; exact hB)]
  simp only [execInstr, r1]
  have h12' : s1.natMem 12 = 0 := (r4 12 (by norm_num) (by norm_num)).trans h12
  have h9' : s1.natMem 9 = x / 2 := r3
  have h8' : s1.natMem 8 = x % 2 := r2
  refine ⟨by omega, ?_, ?_, ?_, r5⟩
  · rw [Function.update_self, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      h9', h12']
    rfl
  · rw [Function.update_of_ne ht, Function.update_self, h8', h12']
    rfl
  · intro a a8 a9 at'
    rw [Function.update_of_ne a8, Function.update_of_ne at']
    exact r4 a a8 a9

lemma rounds :
    ∀ (j : ℕ), j ≤ 6 → ∀ (M : ℕ → ℕ) (R : ℕ → ℝ), M 10 = 2 → M 11 = 1 → M 12 = 0 →
      ∃ τ, τ ≤ j * (2 * M 8 + 4) ∧
        (planarRAMRun p ⟨base + 5, M, R⟩ τ).pc = base + (5 + 7 * j) ∧
        (planarRAMRun p ⟨base + 5, M, R⟩ τ).natMem 8 = M 8 / 2 ^ j ∧
        (planarRAMRun p ⟨base + 5, M, R⟩ τ).natMem 10 = 2 ∧
        (planarRAMRun p ⟨base + 5, M, R⟩ τ).natMem 11 = 1 ∧
        (planarRAMRun p ⟨base + 5, M, R⟩ τ).natMem 12 = 0 ∧
        (∀ i, i < j → (planarRAMRun p ⟨base + 5, M, R⟩ τ).natMem (46 - 2 * i) = M 8 / 2 ^ i % 2) ∧
        (∀ a, a ≠ 8 → a ≠ 9 → (∀ i, i < j → a ≠ 46 - 2 * i) →
          (planarRAMRun p ⟨base + 5, M, R⟩ τ).natMem a = M a) ∧
        (planarRAMRun p ⟨base + 5, M, R⟩ τ).realMem = R := by
  intro j
  induction j with
  | zero =>
    intro _ M R h10 h11 h12
    exact ⟨0, Nat.zero_le _, rfl, by simp [run_zero], h10, h11, h12, fun i hi => by omega,
      fun a _ _ _ => rfl, rfl⟩
  | succ j ih =>
    intro hj M R h10 h11 h12
    obtain ⟨τ, hτ, q1, q2, q10, q11, q12, qbits, qfr, qr⟩ := ih (by omega) M R h10 h11 h12
    set sj := planarRAMRun p ⟨base + 5, M, R⟩ τ with hsj
    obtain ⟨pcj, N, Rr⟩ := sj
    simp only at q1 q2 q10 q11 q12 qbits qfr qr
    subst q1
    obtain ⟨r1, r2, r3, r4, r5⟩ := round_step p base hcode j (by omega) N Rr q10 q11 q12
    have hx : N 8 ≤ M 8 := by rw [q2]; exact Nat.div_le_self _ _
    refine ⟨τ + (4 * (N 8 / 2) + 4), ?_, ?_⟩
    · have : 4 * (N 8 / 2) + 4 ≤ 2 * M 8 + 4 := by omega
      nlinarith
    rw [run_add, ← hsj]
    have hdiv : N 8 / 2 = M 8 / 2 ^ (j + 1) := by
      rw [q2, Nat.div_div_eq_div_mul, pow_succ]
    refine ⟨r1, by rw [r2, hdiv], ?_, ?_, ?_, ?_, ?_, r5.trans qr⟩
    · rw [r4 10 (by norm_num) (by norm_num) (by omega), q10]
    · rw [r4 11 (by norm_num) (by norm_num) (by omega), q11]
    · rw [r4 12 (by norm_num) (by norm_num) (by omega), q12]
    · intro i hi
      by_cases hij : i = j
      · subst hij; rw [r3, q2]
      · rw [r4 (46 - 2 * i) (by omega) (by omega) (by omega), qbits i (by omega)]
    · intro a a8 a9 hne
      rw [r4 a a8 a9 (hne j (by omega)), qfr a a8 a9 (fun i hi => hne i (by omega))]

theorem unpack_fragment (s : PlanarRAMState) (hpc : s.pc = base)
    (k b2 b3 b4 b5 b6 b7 : ℕ) (h2 : b2 ≤ 1) (h3 : b3 ≤ 1) (h4 : b4 ≤ 1) (h5 : b5 ≤ 1) (h6 : b6 ≤ 1)
    (h7 : b7 ≤ 1)
    (hP : s.natMem 1 = 64 * k + 32 * b2 + 16 * b3 + 8 * b4 + 4 * b5 + 2 * b6 + b7) :
    ∃ τ, τ ≤ 12 * s.natMem 1 + 30 ∧
      (planarRAMRun p s τ).pc = base + 48 ∧
      (planarRAMRun p s τ).natMem 32 = s.natMem 0 ∧ (planarRAMRun p s τ).natMem 34 = k ∧
      (planarRAMRun p s τ).natMem 36 = b2 ∧ (planarRAMRun p s τ).natMem 38 = b3 ∧
      (planarRAMRun p s τ).natMem 40 = b4 ∧ (planarRAMRun p s τ).natMem 42 = b5 ∧
      (planarRAMRun p s τ).natMem 44 = b6 ∧ (planarRAMRun p s τ).natMem 46 = b7 ∧
      (∀ a, a ≠ 8 → a ≠ 9 → a ≠ 10 → a ≠ 11 → a ≠ 12 → a ≠ 32 → a ≠ 34 → a ≠ 36 → a ≠ 38 →
        a ≠ 40 → a ≠ 42 → a ≠ 44 → a ≠ 46 → (planarRAMRun p s τ).natMem a = s.natMem a) ∧
      (planarRAMRun p s τ).realMem = s.realMem := by
  have c : ∀ i, i < 5 → p[base + i]? = ([natConst 10 2, natConst 11 1, natConst 12 0,
      natAdd 32 0 12, natAdd 8 1 12] : List PlanarRAMInstruction)[i]? := by
    intro i hi
    rw [hcode i (by simp; omega)]
    interval_cases i <;> rfl
  have c0 := c 0 (by norm_num); have c1 := c 1 (by norm_num); have c2 := c 2 (by norm_num)
  have c3 := c 3 (by norm_num); have c4 := c 4 (by norm_num)
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, add_zero] at c0 c1 c2 c3 c4
  let M1 := Function.update (Function.update (Function.update (Function.update
    (Function.update s.natMem 10 2) 11 1) 12 0) 32 (s.natMem 0)) 8 (s.natMem 1)
  have e : planarRAMRun p s 5 = ⟨base + 5, M1, s.realMem⟩ := by
    rw [show planarRAMRun p s 5 = planarRAMRun p s (0 + 1 + 1 + 1 + 1 + 1) from rfl,
      run_succ, step_exec p _ _ (by rw [hpc]; exact c0), run_succ,
      step_exec p _ _ (by simpa [execInstr, hpc] using c1), run_succ,
      step_exec p _ _ (by simpa [execInstr, hpc] using c2), run_succ,
      step_exec p _ _ (by simpa [execInstr, hpc] using c3), run_succ,
      step_exec p _ _ (by simpa [execInstr, hpc] using c4), run_zero]
    simp only [execInstr, hpc, M1, Function.update_self,
      Function.update_of_ne (show (0:ℕ) ≠ 12 by norm_num), Function.update_of_ne (show (0:ℕ) ≠ 11 by norm_num),
      Function.update_of_ne (show (0:ℕ) ≠ 10 by norm_num), Function.update_of_ne (show (12:ℕ) ≠ 32 by norm_num),
      Function.update_of_ne (show (1:ℕ) ≠ 32 by norm_num), Function.update_of_ne (show (1:ℕ) ≠ 12 by norm_num),
      Function.update_of_ne (show (1:ℕ) ≠ 11 by norm_num), Function.update_of_ne (show (1:ℕ) ≠ 10 by norm_num),
      add_zero]
  have m10 : M1 10 = 2 := by simp [M1]
  have m11 : M1 11 = 1 := by simp [M1]
  have m12 : M1 12 = 0 := by simp [M1]
  have m8 : M1 8 = s.natMem 1 := by simp [M1]
  have m32 : M1 32 = s.natMem 0 := by simp [M1]
  have mfr : ∀ a, a ≠ 8 → a ≠ 10 → a ≠ 11 → a ≠ 12 → a ≠ 32 → M1 a = s.natMem a := by
    intro a a8 a10 a11 a12 a32
    simp only [M1, Function.update_of_ne a8, Function.update_of_ne a32, Function.update_of_ne a12,
      Function.update_of_ne a11, Function.update_of_ne a10]
  obtain ⟨τ1, hτ1, q1, q2, q10, q11, q12, qbits, qfr, qr⟩ :=
    rounds p base hcode 6 le_rfl M1 s.realMem m10 m11 m12
  have hfin : p[base + 47]? = some (natAdd 34 8 12) := by
    rw [hcode 47 (by simp)]; rfl
  refine ⟨5 + τ1 + 1, by rw [m8] at hτ1; omega, ?_⟩
  rw [run_succ_right, run_add, e]
  rw [step_exec p _ _ (by rw [q1]; exact hfin)]
  simp only [execInstr, q1]
  rw [m8] at q2 qbits
  have b0 := qbits 0 (by norm_num); have b1 := qbits 1 (by norm_num); have b2' := qbits 2 (by norm_num)
  have b3' := qbits 3 (by norm_num); have b4' := qbits 4 (by norm_num); have b5' := qbits 5 (by norm_num)
  norm_num at b0 b1 b2' b3' b4' b5' q2
  rw [hP] at b0 b1 b2' b3' b4' b5' q2
  have f32 := qfr 32 (by norm_num) (by norm_num) (fun i hi => by omega)
  have A := arith_unpack k b2 b3 b4 b5 b6 b7 h2 h3 h4 h5 h6 h7
  obtain ⟨A0, A7, A6, A5, A4, A3, A2⟩ := A
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, qr⟩
  · rw [Function.update_of_ne (by norm_num), f32, m32]
  · rw [Function.update_self, q2, q12, A0, add_zero]
  · rw [Function.update_of_ne (by norm_num), b5', A2]
  · rw [Function.update_of_ne (by norm_num), b4', A3]
  · rw [Function.update_of_ne (by norm_num), b3', A4]
  · rw [Function.update_of_ne (by norm_num), b2', A5]
  · rw [Function.update_of_ne (by norm_num), b1, A6]
  · rw [Function.update_of_ne (by norm_num), b0, A7]
  · intro a a8 a9 a10 a11 a12 a32 a34 a36 a38 a40 a42 a44 a46
    rw [Function.update_of_ne a34, qfr a a8 a9 (fun i hi => by omega),
      mfr a a8 a10 a11 a12 a32]

end

end HV

open WilliamsonShmoys PlanarRAMInstruction

theorem solution (p : List PlanarRAMInstruction) (base : ℕ)
    (hcode : CodeAt p base
      [natConst 10 2, natConst 11 1, natConst 12 0, natAdd 32 0 12, natAdd 8 1 12, natConst 9 0, natBranch 10 8 (base + 7) (base + 10), natSub 8 8 10, natAdd 9 9 11, jump (base + 6), natAdd 46 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (base + 14) (base + 17), natSub 8 8 10, natAdd 9 9 11, jump (base + 13), natAdd 44 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (base + 21) (base + 24), natSub 8 8 10, natAdd 9 9 11, jump (base + 20), natAdd 42 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (base + 28) (base + 31), natSub 8 8 10, natAdd 9 9 11, jump (base + 27), natAdd 40 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (base + 35) (base + 38), natSub 8 8 10, natAdd 9 9 11, jump (base + 34), natAdd 38 8 12, natAdd 8 9 12, natConst 9 0, natBranch 10 8 (base + 42) (base + 45), natSub 8 8 10, natAdd 9 9 11, jump (base + 41), natAdd 36 8 12, natAdd 8 9 12, natAdd 34 8 12]) (s : PlanarRAMState) (hpc : s.pc = base)
    (k b2 b3 b4 b5 b6 b7 : ℕ) (h2 : b2 ≤ 1) (h3 : b3 ≤ 1) (h4 : b4 ≤ 1) (h5 : b5 ≤ 1) (h6 : b6 ≤ 1)
    (h7 : b7 ≤ 1)
    (hP : s.natMem 1 = 64 * k + 32 * b2 + 16 * b3 + 8 * b4 + 4 * b5 + 2 * b6 + b7) :
    ∃ τ, τ ≤ 12 * s.natMem 1 + 30 ∧
      (planarRAMRun p s τ).pc = base + 48 ∧
      (planarRAMRun p s τ).natMem 32 = s.natMem 0 ∧ (planarRAMRun p s τ).natMem 34 = k ∧
      (planarRAMRun p s τ).natMem 36 = b2 ∧ (planarRAMRun p s τ).natMem 38 = b3 ∧
      (planarRAMRun p s τ).natMem 40 = b4 ∧ (planarRAMRun p s τ).natMem 42 = b5 ∧
      (planarRAMRun p s τ).natMem 44 = b6 ∧ (planarRAMRun p s τ).natMem 46 = b7 ∧
      (∀ a, a ≠ 8 → a ≠ 9 → a ≠ 10 → a ≠ 11 → a ≠ 12 → a ≠ 32 → a ≠ 34 → a ≠ 36 → a ≠ 38 →
        a ≠ 40 → a ≠ 42 → a ≠ 44 → a ≠ 46 → (planarRAMRun p s τ).natMem a = s.natMem a) ∧
      (planarRAMRun p s τ).realMem = s.realMem :=
  HV.unpack_fragment p base hcode s hpc k b2 b3 b4 b5 b6 b7 h2 h3 h4 h5 h6 h7 hP
