-- Prove2me | solution 1 for WorkbookSource.problem_13696
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:39:26.792987+00:00
-- url     : https://prove2.me/submissions/e55a2163-497a-4020-b7b0-2bf5879ab9ee

/- InternLM Lean-Workbook, lean_workbook_13696, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x : ℝ) : Real.sin (70 * π / 180) = Real.cos (20 * π / 180)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | rw [← Real.sin_pi_div_two_sub]
      congr 1
      ring_nf
  | solve
    | rw [← Real.sin_pi_div_two_sub, sub_eq_add_neg]
      congr 1
      ring
  | solve
    | rw [← Real.cos_pi_div_two_sub, show 20 * π / 180 = π / 2 - 70 * π / 180 by ring]
  | solve
    | rw [← Real.sin_pi_div_two_sub, show (π / 2) - (20 * π / 180) = 70 * π / 180 by linarith]
  | solve
    | rw [← Real.sin_pi_div_two_sub, show (π / 2) - (20 * π / 180) = 70 * π / 180 by nlinarith]
example : (∀ (x : ℝ), Real.sin (70 * π / 180) = Real.cos (20 * π / 180)) := @solution
#print axioms solution
