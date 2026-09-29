-- Prove2me | solution 1 for WorkbookSource.problem_52170
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:12:44.469242+00:00
-- url     : https://prove2.me/submissions/fc7b129a-91db-4eb5-bdc8-47fc6778cddb

/- InternLM Lean-Workbook, lean_workbook_52170, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (a b c : ℝ) : 3 * (a * b + b * c + c * a) / (a + b + c) ^ 2 ≤ 1  := by
  by_cases hs : a + b + c = 0
  · simp [hs]
  · apply (div_le_one (sq_pos_of_ne_zero hs)).2
    nlinarith [sq_nonneg (a-b), sq_nonneg (b-c), sq_nonneg (c-a)]

example : (∀ (a b c : ℝ), 3 * (a * b + b * c + c * a) / (a + b + c) ^ 2 ≤ 1) := @solution
#print axioms solution
