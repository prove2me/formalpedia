-- Prove2me | solution 1 for WorkbookSource.problem_32941
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:59:25.600735+00:00
-- url     : https://prove2.me/submissions/e939df0e-d6dd-4888-bc64-9a8c9f2e7f03

/- InternLM Lean-Workbook, lean_workbook_32941, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) (habc : a * b + b * c + c * a = 3) : a ^ 2 + b ^ 2 + c ^ 2 + 15 ≥ 6 * (a + b + c)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | nlinarith [sq_nonneg (a + b + c - 3)]
  | solve
    | nlinarith [sq_nonneg (a + b + c - 3), habc]
  | solve
    | have := sq_nonneg (a + b + c - 3)
      linarith [habc]
  | solve
    | have := sq_nonneg (a + b + c - 3)
      linarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
  | solve
    | have := sq_nonneg (a + b + c - 3)
      nlinarith [habc]
  | solve
    | have := sq_nonneg (a + b + c - 3)
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
example : (∀ (a b c : ℝ) (habc : a * b + b * c + c * a = 3), a ^ 2 + b ^ 2 + c ^ 2 + 15 ≥ 6 * (a + b + c)) := @solution
#print axioms solution
