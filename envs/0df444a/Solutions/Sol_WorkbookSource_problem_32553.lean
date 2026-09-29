-- Prove2me | solution 1 for WorkbookSource.problem_32553
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:05:55.203421+00:00
-- url     : https://prove2.me/submissions/acbb6c13-808c-4324-8e3b-65512cb04768

/- InternLM Lean-Workbook, lean_workbook_32553, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxRecDepth 10000
set_option exponentiation.threshold 4096
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 13 ^ 2009 * 9999 ^ 6 * 3 ^ 12 ≡ 93 [MOD 100]  := by
  norm_num

example : (13 ^ 2009 * 9999 ^ 6 * 3 ^ 12 ≡ 93 [MOD 100]) := @solution
#print axioms solution
