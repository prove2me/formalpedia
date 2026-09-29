-- Prove2me | solution 1 for WorkbookSource.problem_53209
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:10:06.679416+00:00
-- url     : https://prove2.me/submissions/5d64fbae-cd5e-447c-b17e-7137c3e5adab

/- InternLM Lean-Workbook, lean_workbook_53209, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution :
  7 * 333 - 1994 = 337  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | norm_num at *
  | solve
    | rw [Nat.mul_comm]
  | solve
    | simp only [mul_one]
  | solve
    | norm_num [Nat.sub_sub]
example : (7 * 333 - 1994 = 337) := @solution
#print axioms solution
