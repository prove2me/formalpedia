-- Prove2me | solution 1 for WorkbookSource.problem_3709
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:15:10.821762+00:00
-- url     : https://prove2.me/submissions/4cd4e2da-335f-415f-81a0-86c6470af642

/- InternLM Lean-Workbook, lean_workbook_3709, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution : (10:ℝ)^(Real.logb 10 7) = 7  := by
  first
  | solve
    | rw [Real.rpow_logb] <;> norm_num
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | simp [← Real.rpow_logb]
  | solve
    | rw [Real.rpow_logb] <;> norm_num
  | solve
    | exact eq_of_div_eq_one (by norm_num)
example : ((10:ℝ)^(Real.logb 10 7) = 7) := @solution
#print axioms solution
