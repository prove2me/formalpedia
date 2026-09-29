-- Prove2me | solution 1 for WorkbookSource.problem_10411
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:20.226965+00:00
-- url     : https://prove2.me/submissions/c6ddc615-78ee-4313-a26c-e5590c1ff940

/- InternLM Lean-Workbook, lean_workbook_10411, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution :
  (2014^2015) % 121 = 34  := by
  norm_num [Nat.pow_mod]
example : ((2014^2015) % 121 = 34) := @solution
#print axioms solution
