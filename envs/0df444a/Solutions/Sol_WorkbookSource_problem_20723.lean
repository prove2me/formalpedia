-- Prove2me | solution 1 for WorkbookSource.problem_20723
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T21:51:59.455107+00:00
-- url     : https://prove2.me/submissions/62e065ac-b0a8-4c6c-aec2-8ed541dd66f6

/- InternLM Lean-Workbook, lean_workbook_20723, Apache-2.0. Complete source proposition retained. -/
import Mathlib
open Real Nat
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
theorem solution (x y : ℝ) (h : x + y + 1 = 0) :
  2 * (x^5 + y^5 + 1) = 5 * x * y * (x^2 + y^2 + 1)  := by
  first
  | solve
    | ring
  | solve
    | intros; ring
  | solve
    | have : x = -(y + 1) := by linarith
      rw [this]
      ring
  | solve
    | have h' : x = -(y + 1) := by linarith
      rw [h']
      ring
  | solve
    | have h1 : x = -(y + 1) := by linarith
      rw [h1]
      ring
  | solve
    | have : y = -(x + 1) := by linarith
      simp [this]
      ring
  | solve
    | have : x = -(y + 1) := by nlinarith
      rw [this]
      ring
  | solve
    | have h' : x = -(y + 1) := by nlinarith
      rw [h']
      ring
  | solve
    | have h1 : x = -(y + 1) := by nlinarith
      rw [h1]
      ring
  | solve
    | have : y = -(x + 1) := by nlinarith
      simp [this]
      ring
example : (∀ (x y : ℝ) (h : x + y + 1 = 0), 2 * (x^5 + y^5 + 1) = 5 * x * y * (x^2 + y^2 + 1)) := @solution
#print axioms solution
