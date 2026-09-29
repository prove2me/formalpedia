-- Prove2me | solution 1 for WorkbookSource.problem_22195
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:57:11.097672+00:00
-- url     : https://prove2.me/submissions/ce6c75a4-d94f-4f67-899a-047ff08bc00d

/- InternLM Lean-Workbook, lean_workbook_22195, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : (1000 : ℝ) ^ 1000 > 1001 ^ 999  := by
  norm_num

example : ((1000 : ℝ) ^ 1000 > 1001 ^ 999) := @solution
#print axioms solution
