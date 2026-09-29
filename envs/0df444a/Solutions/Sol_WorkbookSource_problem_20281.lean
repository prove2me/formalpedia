-- Prove2me | solution 1 for WorkbookSource.problem_20281
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:51:58.150402+00:00
-- url     : https://prove2.me/submissions/564a1b11-68ce-46ac-9dfe-7ef01352ffc6

/- InternLM Lean-Workbook, lean_workbook_20281, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 100^117 > 117^100  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | norm_num [pow_one]
  | solve
    | norm_num [Nat.pow]
  | solve
    | norm_num [Nat.pow_mod]
  | solve
    | norm_num [Nat.pow_succ]
example : (100^117 > 117^100) := @solution
#print axioms solution
