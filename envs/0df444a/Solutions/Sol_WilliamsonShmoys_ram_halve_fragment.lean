-- Prove2me | solution 1 for WilliamsonShmoys.ram_halve_fragment
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T15:24:51.18673+00:00
-- url     : https://prove2.me/submissions/03713724-5698-4ad8-a3a6-efa8dc6f95fa

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

end HV

open WilliamsonShmoys PlanarRAMInstruction

theorem solution (p : List PlanarRAMInstruction) (base : ℕ)
    (hcode : CodeAt p base
      [natConst 9 0, natBranch 10 8 (base + 2) (base + 5), natSub 8 8 10, natAdd 9 9 11, jump (base + 1)]) (s : PlanarRAMState) (hpc : s.pc = base) (h10 : s.natMem 10 = 2)
    (h11 : s.natMem 11 = 1) :
    let x := s.natMem 8
    let s' := planarRAMRun p s (4 * (x / 2) + 2)
    s'.pc = base + 5 ∧ s'.natMem 8 = x % 2 ∧ s'.natMem 9 = x / 2 ∧
      (∀ a, a ≠ 8 → a ≠ 9 → s'.natMem a = s.natMem a) ∧ s'.realMem = s.realMem :=
  HV.halve_fragment p base hcode s hpc h10 h11
