-- Prove2me | solution 1 for WorkbookSource.problem_33418
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:05:56.685732+00:00
-- url     : https://prove2.me/submissions/55594c03-2f1a-4e1a-acf7-4bdf6811dff1

/- InternLM Lean-Workbook, lean_workbook_33418, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (θ : ℝ) : (1 + Real.sin θ) * (1 + Real.cos θ) = 1 / 2 * (1 + Real.sin θ + Real.cos θ)^2  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | linarith [sin_sq_add_cos_sq θ]
  | solve
    | ring_nf
      simp [Real.sin_sq, Real.cos_sq]
      ring_nf
  | solve
    | nlinarith [sin_sq_add_cos_sq θ]
example : (∀ (θ : ℝ), (1 + Real.sin θ) * (1 + Real.cos θ) = 1 / 2 * (1 + Real.sin θ + Real.cos θ)^2) := @solution
#print axioms solution
