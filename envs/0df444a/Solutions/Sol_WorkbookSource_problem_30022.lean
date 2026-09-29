-- Prove2me | solution 1 for WorkbookSource.problem_30022
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:05:51.434952+00:00
-- url     : https://prove2.me/submissions/dc013539-d081-4a6a-bcfe-b5dc96c1f249

/- InternLM Lean-Workbook, lean_workbook_30022, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution :
  (333^555 + 555^777 + 777^333) % 13 = 5  := by
  norm_num

example : ((333^555 + 555^777 + 777^333) % 13 = 5) := @solution
#print axioms solution
