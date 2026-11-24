-- Prove2me | solution 1 for WilliamsonShmoys.ram_square_fragment
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T12:21:09.411905+00:00
-- url     : https://prove2.me/submissions/2210711b-1df9-474f-b2b7-ecb85ee8723f

import Mathlib
import Definitions.Def_WilliamsonShmoys_RAMExec

set_option autoImplicit false

namespace SQ
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
    [natConst 4 1, natConst 2 2, natConst 3 0, natBranch 0 3 (base + 7) (base + 4),
      natAdd 2 2 0, natAdd 3 3 4, jump (base + 3)])
include hcode

lemma code_at (i : ℕ) (hi : i < 7) :
    p[base + i]? = ([natConst 4 1, natConst 2 2, natConst 3 0, natBranch 0 3 (base + 7) (base + 4),
      natAdd 2 2 0, natAdd 3 3 4, jump (base + 3)] : List PlanarRAMInstruction)[i]? :=
  hcode i (by simpa using hi)

/-- The loop part: from the loop head with counter `i` and accumulator `2 + i*n`. -/
lemma sq_loop (n : ℕ) :
    ∀ (d i : ℕ) (M : ℕ → ℕ) (R : ℕ → ℝ), i + d = n → M 0 = n → M 3 = i → M 4 = 1 →
      M 2 = 2 + i * n →
      let s' := planarRAMRun p ⟨base + 3, M, R⟩ (4 * d + 1)
      s'.pc = base + 7 ∧ s'.natMem 2 = 2 + n * n ∧ s'.natMem 3 = n ∧
        (∀ a, a ≠ 2 → a ≠ 3 → s'.natMem a = M a) ∧ s'.realMem = R := by
  intro d
  induction d with
  | zero =>
    intro i M R hi h0 h3 h4 h2
    have hb : p[base + 3]? = some (natBranch 0 3 (base + 7) (base + 4)) := by
      simpa using code_at p base hcode 3 (by norm_num)
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [run_succ, run_zero, step_exec p _ _ hb]
    simp only [execInstr, h0, h3]
    have : i = n := by omega
    subst this
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp_all
  | succ d ih =>
    intro i M R hi h0 h3 h4 h2
    have hb : p[base + 3]? = some (natBranch 0 3 (base + 7) (base + 4)) := by
      simpa using code_at p base hcode 3 (by norm_num)
    have h4' : p[base + 4]? = some (natAdd 2 2 0) := by simpa using code_at p base hcode 4 (by norm_num)
    have h5' : p[base + 5]? = some (natAdd 3 3 4) := by simpa using code_at p base hcode 5 (by norm_num)
    have h6' : p[base + 6]? = some (jump (base + 3)) := by simpa using code_at p base hcode 6 (by norm_num)
    have hlt : ¬ n ≤ i := by omega
    -- four steps of the body bring us back to the loop head
    have e : planarRAMRun p ⟨base + 3, M, R⟩ 4 =
        ⟨base + 3, Function.update (Function.update M 2 (M 2 + M 0)) 3 (M 3 + M 4), R⟩ := by
      rw [show planarRAMRun p ⟨base + 3, M, R⟩ 4 = planarRAMRun p ⟨base + 3, M, R⟩ (0 + 1 + 1 + 1 + 1) from rfl,
        run_succ, step_exec p _ _ hb]
      simp only [execInstr, h0, h3, if_neg hlt]
      rw [run_succ, step_exec p _ _ h4', run_succ]
      simp only [execInstr]
      rw [step_exec p _ _ (by simpa using h5'), run_succ]
      simp only [execInstr]
      rw [step_exec p _ _ (by simpa using h6'), run_zero]
      simp only [execInstr, Function.update_of_ne (show (3:ℕ) ≠ 2 by norm_num),
        Function.update_of_ne (show (4:ℕ) ≠ 2 by norm_num), h0, h3]
    rw [show 4 * (d + 1) + 1 = 4 + (4 * d + 1) by ring, run_add, e]
    have hM : ∀ a, a ≠ 2 → a ≠ 3 →
        Function.update (Function.update M 2 (M 2 + M 0)) 3 (M 3 + M 4) a = M a := by
      intro a ha2 ha3
      rw [Function.update_of_ne ha3, Function.update_of_ne ha2]
    obtain ⟨r1, r2, r3, r4, r5⟩ := ih (i + 1)
      (Function.update (Function.update M 2 (M 2 + M 0)) 3 (M 3 + M 4)) R (by omega)
      (by rw [hM 0 (by norm_num) (by norm_num), h0])
      (by simp [h3, h4])
      (by rw [hM 4 (by norm_num) (by norm_num), h4])
      (by simp [h2, h0]; ring)
    exact ⟨r1, r2, r3, fun a ha2 ha3 => (r4 a ha2 ha3).trans (hM a ha2 ha3), r5⟩

theorem sq_fragment (s : PlanarRAMState) (hpc : s.pc = base) :
    let n := s.natMem 0
    let s' := planarRAMRun p s (4 * n + 4)
    s'.pc = base + 7 ∧ s'.natMem 2 = 2 + n * n ∧ s'.natMem 3 = n ∧ s'.natMem 4 = 1 ∧
      (∀ a, a ≠ 2 → a ≠ 3 → a ≠ 4 → s'.natMem a = s.natMem a) ∧ s'.realMem = s.realMem := by
  intro n
  have c0 : p[base + 0]? = some (natConst 4 1) := by simpa using code_at p base hcode 0 (by norm_num)
  have c1 : p[base + 1]? = some (natConst 2 2) := by simpa using code_at p base hcode 1 (by norm_num)
  have c2 : p[base + 2]? = some (natConst 3 0) := by simpa using code_at p base hcode 2 (by norm_num)
  let M1 := Function.update (Function.update (Function.update s.natMem 4 1) 2 2) 3 0
  have e : planarRAMRun p s 3 = ⟨base + 3, M1, s.realMem⟩ := by
    rw [show planarRAMRun p s 3 = planarRAMRun p s (0 + 1 + 1 + 1) from rfl, run_succ,
      step_exec p _ _ (by rw [hpc]; simpa using c0), run_succ,
      step_exec p _ _ (by simpa [execInstr, hpc] using c1), run_succ,
      step_exec p _ _ (by simpa [execInstr, hpc] using c2), run_zero]
    simp only [execInstr, hpc, M1]
  rw [show 4 * n + 4 = 3 + (4 * n + 1) by ring, run_add, e]
  have hM1 : ∀ a, a ≠ 2 → a ≠ 3 → a ≠ 4 → M1 a = s.natMem a := by
    intro a h2 h3 h4
    simp only [M1, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h4]
  obtain ⟨r1, r2, r3, r4, r5⟩ := sq_loop p base hcode n n 0 M1 s.realMem (by omega)
    (by rw [hM1 0 (by norm_num) (by norm_num) (by norm_num)])
    (by simp [M1]) (by simp [M1]) (by simp [M1])
  refine ⟨r1, r2, r3, ?_, fun a h2 h3 h4 => (r4 a h2 h3).trans (hM1 a h2 h3 h4), r5⟩
  rw [r4 4 (by norm_num) (by norm_num)]
  simp [M1]

end

end SQ

open WilliamsonShmoys PlanarRAMInstruction

theorem solution (p : List PlanarRAMInstruction) (base : ℕ)
    (hcode : CodeAt p base
      [natConst 4 1, natConst 2 2, natConst 3 0, natBranch 0 3 (base + 7) (base + 4), natAdd 2 2 0, natAdd 3 3 4, jump (base + 3)]) (s : PlanarRAMState) (hpc : s.pc = base) :
    let n := s.natMem 0
    let s' := planarRAMRun p s (4 * n + 4)
    s'.pc = base + 7 ∧ s'.natMem 2 = 2 + n * n ∧ s'.natMem 3 = n ∧ s'.natMem 4 = 1 ∧
      (∀ a, a ≠ 2 → a ≠ 3 → a ≠ 4 → s'.natMem a = s.natMem a) ∧ s'.realMem = s.realMem :=
  SQ.sq_fragment p base hcode s hpc
