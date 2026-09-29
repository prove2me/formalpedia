-- Prove2me | solution 1 for WorkbookSource.problem_11845
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:25.245135+00:00
-- url     : https://prove2.me/submissions/87e8feca-8814-4743-9e9c-54f46e4665b9

/- InternLM Lean-Workbook, lean_workbook_11845, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : ∀ x : ℝ, 0 < x ∧ x < π/2 → 0 ≤ 2 * Real.sin x * Real.cos x ∧ 2 * Real.sin x * Real.cos x ≤ 1  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | intro x h
      constructor
      have h1 : 0 ≤ Real.sin (2 * x) := Real.sin_nonneg_of_mem_Icc ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
      rw [Real.sin_two_mul] at h1
      have h2 : 0 ≤ 2 * Real.sin x * Real.cos x := by linarith
      exact h2
      have h1 : Real.sin (2 * x) ≤ 1 := Real.sin_le_one (2 * x)
      rw [Real.sin_two_mul] at h1
      have h2 : 2 * Real.sin x * Real.cos x ≤ 1 := by linarith
      exact h2
  | solve
    | intro x h
      constructor
      have h1 : 0 ≤ Real.sin (2 * x) := Real.sin_nonneg_of_mem_Icc ⟨by nlinarith [h.1, h.2], by nlinarith [h.1, h.2]⟩
      rw [Real.sin_two_mul] at h1
      have h2 : 0 ≤ 2 * Real.sin x * Real.cos x := by nlinarith
      exact h2
      have h1 : Real.sin (2 * x) ≤ 1 := Real.sin_le_one (2 * x)
      rw [Real.sin_two_mul] at h1
      have h2 : 2 * Real.sin x * Real.cos x ≤ 1 := by nlinarith
      exact h2
example : (∀ x : ℝ, 0 < x ∧ x < π/2 → 0 ≤ 2 * Real.sin x * Real.cos x ∧ 2 * Real.sin x * Real.cos x ≤ 1) := @solution
#print axioms solution
