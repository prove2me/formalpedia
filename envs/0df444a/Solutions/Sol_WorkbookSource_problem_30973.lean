-- Prove2me | solution 1 for WorkbookSource.problem_30973
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:59:18.698058+00:00
-- url     : https://prove2.me/submissions/aa43d1f3-cecf-4938-8217-dd9c05900860

/- InternLM Lean-Workbook, lean_workbook_30973, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 31 ^ 11 < 17 ^ 14  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | norm_num [pow_mul]
  | solve
    | norm_num [pow_zero]
  | solve
    | norm_num [Int.coe_nat_pow]
  | solve
    | norm_num [pow_succ, pow_mul]
example : (31 ^ 11 < 17 ^ 14) := @solution
#print axioms solution
