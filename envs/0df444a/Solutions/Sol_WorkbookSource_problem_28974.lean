-- Prove2me | solution 1 for WorkbookSource.problem_28974
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:57:18.363468+00:00
-- url     : https://prove2.me/submissions/ff47bde3-07c9-4509-b622-b2510d370741

/- InternLM Lean-Workbook, lean_workbook_28974, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 23 * 4 - 1 - 5 = 86  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rw [mul_comm]
  | solve
    | simp [Sub.sub]
  | solve
    | simp [Nat.sub_sub]
  | solve
    | norm_num [Nat.gcd]
example : (23 * 4 - 1 - 5 = 86) := @solution
#print axioms solution
