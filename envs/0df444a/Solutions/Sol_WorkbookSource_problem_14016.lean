-- Prove2me | solution 1 for WorkbookSource.problem_14016
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:29.869438+00:00
-- url     : https://prove2.me/submissions/7d66bf42-6b2a-4fef-8223-c6f4534f97a0

/- InternLM Lean-Workbook, lean_workbook_14016, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) (h : sin x + cos x = 6/5) : sin (2 * x) = 11/25  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [sin_two_mul, h]
      nlinarith [sin_sq_add_cos_sq x, h]
  | solve
    | simp [sin_two_mul, cos_two_mul]
      nlinarith [sin_sq_add_cos_sq x]
example : (∀ (x : ℝ) (h : sin x + cos x = 6/5), sin (2 * x) = 11/25) := @solution
#print axioms solution
