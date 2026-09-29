-- Prove2me | solution 1 for WorkbookSource.problem_8627
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:50:06.563694+00:00
-- url     : https://prove2.me/submissions/874b1ddb-bad9-4756-9ba8-e3c82a9819bb

/- InternLM Lean-Workbook, lean_workbook_8627, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) (hx : -1 < x) : Real.log (x + 1) ≤ x  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | linarith [log_le_sub_one_of_pos (by linarith : 0 < x + 1)]
  | solve
    | refine' (log_le_sub_one_of_pos _).trans _
      linarith
      linarith [hx]
  | solve
    | refine' (Real.log_le_sub_one_of_pos _).trans _
      linarith
      linarith
  | solve
    | nlinarith [Real.log_le_sub_one_of_pos (by linarith : 0 < x + 1)]
  | solve
    | nlinarith [log_le_sub_one_of_pos (by nlinarith : 0 < x + 1)]
  | solve
    | refine' (log_le_sub_one_of_pos _).trans _
      nlinarith
      nlinarith [hx]
  | solve
    | refine' (Real.log_le_sub_one_of_pos _).trans _
      nlinarith
      nlinarith
example : (∀ (x : ℝ) (hx : -1 < x), Real.log (x + 1) ≤ x) := @solution
#print axioms solution
