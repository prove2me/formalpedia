-- Prove2me | solution 1 for WorkbookSource.problem_40553
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:43:48.436183+00:00
-- url     : https://prove2.me/submissions/1730bb5f-8062-4fb4-b9f4-9ad2745e6ed9

/- InternLM Lean-Workbook, lean_workbook_40553, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y : ℝ) : |x - y| = if x > y then x - y else y - x  := by
  first
  | solve
    | split_ifs with h
      · exact abs_of_pos (sub_pos.mpr h)
      · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_gt h))]
        ring
  | solve
    | split_ifs with h
      rw [abs_of_nonneg]
      linarith
      rw [abs_of_nonpos]
      linarith
      linarith
  | solve
    | split_ifs with h
      exact abs_of_nonneg (sub_nonneg.2 h.le)
      rw [abs_of_nonpos]
      linarith
      linarith
example : (∀ (x y : ℝ), |x - y| = if x > y then x - y else y - x) := @solution
#print axioms solution
