-- Prove2me | solution 1 for WorkbookSource.problem_24006
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:53:32.651194+00:00
-- url     : https://prove2.me/submissions/12611e79-808b-447f-b190-943b6d70203d

/- InternLM Lean-Workbook, lean_workbook_24006, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution :
  17 ∣ (3^16 - 2^16)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | norm_num [Nat.pow]
  | solve
    | norm_num [pow_one]
  | solve
    | norm_num [Nat.sub_sub]
  | solve
    | norm_num [Nat.dvd_sub]
example : (17 ∣ (3^16 - 2^16)) := @solution
#print axioms solution
