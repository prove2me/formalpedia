-- Prove2me | solution 1 for WorkbookSource.problem_31194
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:05:53.196311+00:00
-- url     : https://prove2.me/submissions/2e7342d2-e6c4-4c3a-a24b-6a33c49d0722

/- InternLM Lean-Workbook, lean_workbook_31194, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : (2^(2017):ℝ) * (1/4)^1008 = 2  := by
  norm_num

example : ((2^(2017):ℝ) * (1/4)^1008 = 2) := @solution
#print axioms solution
