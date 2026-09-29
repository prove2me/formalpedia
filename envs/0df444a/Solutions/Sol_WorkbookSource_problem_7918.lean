-- Prove2me | solution 1 for WorkbookSource.problem_7918
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:47:34.970346+00:00
-- url     : https://prove2.me/submissions/2860f0de-a35c-4ab5-a3aa-9dac75ca50cf

/- InternLM Lean-Workbook, lean_workbook_7918, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution :
  1 + 56 + 111 + 166 + 221 = 555  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp only [zero_add]
  | solve
    | simp [Nat.add_assoc]
  | solve
    | simp [Nat.add_left_comm]
  | solve
    | simp only [Nat.succ_pos']
example : (1 + 56 + 111 + 166 + 221 = 555) := @solution
#print axioms solution
