-- Prove2me | solution 1 for WorkbookSource.problem_51028
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:09:58.475391+00:00
-- url     : https://prove2.me/submissions/b0f5ca0e-270a-49dd-a9c8-2c18bd54e988

/- InternLM Lean-Workbook, lean_workbook_51028, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (r : ℝ) : 2 * r * (r ^ 2 * π) = 2 * r ^ 3 * π  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | linarith [r ^ 2]
  | solve
    | linarith only [r]
  | solve
    | rw [mul_assoc]
      ring
  | solve
    | nlinarith [r ^ 2 * π]
  | solve
    | nlinarith [r ^ 2]
  | solve
    | nlinarith only [r]
example : (∀ (r : ℝ), 2 * r * (r ^ 2 * π) = 2 * r ^ 3 * π) := @solution
#print axioms solution
