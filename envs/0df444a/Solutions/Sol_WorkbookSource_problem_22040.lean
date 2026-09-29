-- Prove2me | solution 1 for WorkbookSource.problem_22040
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:57:10.30097+00:00
-- url     : https://prove2.me/submissions/b1ac2adf-4324-431b-90d6-6f32dc56a45e

/- InternLM Lean-Workbook, lean_workbook_22040, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 2 ^ 845 > 3 ^ 362  := by
  norm_num

example : (2 ^ 845 > 3 ^ 362) := @solution
#print axioms solution
