-- Prove2me | solution 1 for WorkbookSource.problem_14402
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:32.152429+00:00
-- url     : https://prove2.me/submissions/67fb8843-5ace-4fb9-875f-6bf509d771cc

/- InternLM Lean-Workbook, lean_workbook_14402, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : 1 * (23 + 4 * 5) = 43  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | congr 1
  | solve
    | rw [one_mul]
  | solve
    | simp only [mul_comm]
  | solve
    | norm_num [Nat.mul_comm]
example : (1 * (23 + 4 * 5) = 43) := @solution
#print axioms solution
