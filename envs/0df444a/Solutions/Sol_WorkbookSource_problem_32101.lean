-- Prove2me | solution 1 for WorkbookSource.problem_32101
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:59:23.504381+00:00
-- url     : https://prove2.me/submissions/ab06a3ab-41d0-4dd5-becf-fc485b22cfc6

/- InternLM Lean-Workbook, lean_workbook_32101, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : (Real.exp 1) ^ (Real.log 2) = 2  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [Real.exp_log]
  | solve
    | rw [← exp_log two_pos]
      norm_num
  | solve
    | exact by norm_num [Real.exp_log]
  | solve
    | rw [← Real.exp_log two_pos]
      simp [Real.log_exp]
example : ((Real.exp 1) ^ (Real.log 2) = 2) := @solution
#print axioms solution
