-- Prove2me | solution 1 for WorkbookSource.problem_33282
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:59:27.027389+00:00
-- url     : https://prove2.me/submissions/ec57c69a-9948-49e4-9184-41c1164f5ee8

/- InternLM Lean-Workbook, lean_workbook_33282, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : ∀ a ≤ (4:ℝ) / 3, (3 * a - 4) * (3 * a - 1) ^ 2 / (50 * (1 + a ^ 2)) ≤ 0  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | intro a h
      apply div_nonpos_of_nonpos_of_nonneg
      nlinarith
      nlinarith
  | solve
    | intro a ha
      apply div_nonpos_of_nonpos_of_nonneg
      nlinarith
      nlinarith
  | solve
    | intro a ha
      apply div_nonpos_of_nonpos_of_nonneg
      any_goals nlinarith
  | solve
    | intro a h
      refine' div_nonpos_of_nonpos_of_nonneg _ _
      nlinarith
      nlinarith
example : (∀ a ≤ (4:ℝ) / 3, (3 * a - 4) * (3 * a - 1) ^ 2 / (50 * (1 + a ^ 2)) ≤ 0) := @solution
#print axioms solution
