-- Prove2me | solution 1 for WorkbookSource.problem_30934
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:05:52.177537+00:00
-- url     : https://prove2.me/submissions/951f3ba7-3be7-4bde-a28a-9612af99a5dc

/- InternLM Lean-Workbook, lean_workbook_30934, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : ∀ x, Real.sqrt (1 - x ^ 2) / (1 + x ^ 2) ≤ 1 / (1 + x ^ 2)  := by
  intro x
  apply div_le_div_of_nonneg_right
  · exact Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg x])
  · positivity

example : (∀ x, Real.sqrt (1 - x ^ 2) / (1 + x ^ 2) ≤ 1 / (1 + x ^ 2)) := @solution
#print axioms solution
