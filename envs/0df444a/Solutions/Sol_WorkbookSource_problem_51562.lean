-- Prove2me | solution 1 for WorkbookSource.problem_51562
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:00.62612+00:00
-- url     : https://prove2.me/submissions/222587bb-c095-4704-a590-7d699aa908da

/- InternLM Lean-Workbook, lean_workbook_51562, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x y : ℝ) : 8 + x * y ≤ Real.sqrt ((8 + x ^ 2) * (8 + y ^ 2))  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | apply le_sqrt_of_sq_le
      nlinarith [sq_nonneg (x - y)]
  | solve
    | have := sq_nonneg (x - y)
      apply le_sqrt_of_sq_le
      linarith
  | solve
    | have := sq_nonneg (x - y)
      apply le_sqrt_of_sq_le
      nlinarith
  | solve
    | have h1 := sq_nonneg (x - y)
      apply le_sqrt_of_sq_le
      nlinarith
  | solve
    | have := sq_nonneg (x - y)
      apply le_sqrt_of_sq_le
      nlinarith
example : (∀ (x y : ℝ), 8 + x * y ≤ Real.sqrt ((8 + x ^ 2) * (8 + y ^ 2))) := @solution
#print axioms solution
