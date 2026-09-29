-- Prove2me | solution 1 for WorkbookSource.problem_12277
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:26.913365+00:00
-- url     : https://prove2.me/submissions/f811c3ce-aa21-4fca-9924-716a4f5125ca

/- InternLM Lean-Workbook, lean_workbook_12277, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : ∀ a : ℝ, (a - 1) ^ 2 * (9 * a ^ 4 - 84 * a ^ 3 + 310 * a ^ 2 - 580 * a + 601) ≥ 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | intro a
      apply mul_nonneg
      apply sq_nonneg
      nlinarith [sq_nonneg (a - 3), sq_nonneg (a - 4)]
  | solve
    | refine' fun a => mul_nonneg _ _
      nlinarith
      nlinarith [sq_nonneg (a - 3), sq_nonneg (a - 5)]
  | solve
    | intro a
      refine' mul_nonneg (sq_nonneg _) _
      nlinarith [sq_nonneg (a - 3), sq_nonneg (a - 4)]
  | solve
    | intro a
      apply mul_nonneg
      exact sq_nonneg (a - 1)
      nlinarith [sq_nonneg (a - 3), sq_nonneg (a - 5)]
example : (∀ a : ℝ, (a - 1) ^ 2 * (9 * a ^ 4 - 84 * a ^ 3 + 310 * a ^ 2 - 580 * a + 601) ≥ 0) := @solution
#print axioms solution
