-- Prove2me | solution 1 for WorkbookSource.problem_28049
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:57:14.094752+00:00
-- url     : https://prove2.me/submissions/e0304031-01bf-4c89-bdfb-c8deb827fb46

/- InternLM Lean-Workbook, lean_workbook_28049, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 5108^35 > 5380^32  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | norm_num [pow_succ]
  | solve
    | norm_num [pow_one, pow_one]
  | solve
    | norm_num [pow_succ, pow_add]
  | solve
    | norm_num [pow_succ, mul_comm]
example : (5108^35 > 5380^32) := @solution
#print axioms solution
