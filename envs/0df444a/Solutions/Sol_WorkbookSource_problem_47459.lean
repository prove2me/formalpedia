-- Prove2me | solution 1 for WorkbookSource.problem_47459
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:17:55.089828+00:00
-- url     : https://prove2.me/submissions/bb1d4690-0c0a-4f15-adcf-c1993751e2ec

/- InternLM Lean-Workbook, lean_workbook_47459, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (k : ℝ) (h : k = -11 - 37 / 2) : ‖2 * k‖ = 59  := by
  first
  | solve
    | rw [h]
      norm_num
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | field_simp [h]
      norm_num
  | solve
    | rw [h]
      ring_nf
      norm_num
  | solve
    | conv_lhs => rw [h]
      norm_num [h]
  | solve
    | rw [h]
      norm_num [abs_of_nonpos]
example : (∀ (k : ℝ) (h : k = -11 - 37 / 2), ‖2 * k‖ = 59) := @solution
#print axioms solution
