-- Prove2me | solution 1 for WorkbookSource.problem_33200
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:59:26.284839+00:00
-- url     : https://prove2.me/submissions/a15a77b5-8b45-4328-826e-bc1828d59c38

/- InternLM Lean-Workbook, lean_workbook_33200, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 2 ^ 19 < 3 ^ 12  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | norm_num [pow_succ]
  | solve
    | norm_num [Nat.gcd_rec]
  | solve
    | norm_num [pow_succ, pow_mul]
  | solve
    | norm_num [pow_succ, pow_succ]
example : (2 ^ 19 < 3 ^ 12) := @solution
#print axioms solution
