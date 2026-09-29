-- Prove2me | solution 1 for WorkbookSource.problem_28151
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:05:50.846544+00:00
-- url     : https://prove2.me/submissions/5fd162fc-46c1-48dc-82d0-9b6cd68571fc

/- InternLM Lean-Workbook, lean_workbook_28151, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : (4:ℝ)^(321) < 3^(421)  := by
  norm_num

example : ((4:ℝ)^(321) < 3^(421)) := @solution
#print axioms solution
