-- Prove2me | solution 1 for WorkbookSource.problem_21690
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:05:49.39765+00:00
-- url     : https://prove2.me/submissions/452fa915-5739-459f-a622-67e82809a552

/- InternLM Lean-Workbook, lean_workbook_21690, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (f : ℝ → ℝ) (hf: f (0:ℝ) = 1 / Real.sqrt 2 * 2 * f (-1/2)) : 2 * f 0 = 2 * Real.sqrt 2 * f (-1/2)  := by
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hc : 1 / Real.sqrt 2 * 2 = Real.sqrt 2 := by
    field_simp
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [hf, hc]
  ring

example : (∀ (f : ℝ → ℝ) (hf: f (0:ℝ) = 1 / Real.sqrt 2 * 2 * f (-1/2)), 2 * f 0 = 2 * Real.sqrt 2 * f (-1/2)) := @solution
#print axioms solution
