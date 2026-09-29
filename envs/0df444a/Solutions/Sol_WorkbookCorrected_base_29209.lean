-- Prove2me | solution 1 for WorkbookCorrected.base_29209
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:12:22.999363+00:00
-- url     : https://prove2.me/submissions/18465aa1-4aba-48b7-b7f4-f1217205e46d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma p2mUpperBound (x y : ℝ) (h : x^2 + 9*y^2 - 4*x + 6*y + 4 = 0) : (4*x - 9*y)/2 ≤ 8  := by
  have hw0 : 0 ≤ (x^2 - 4*x + 9*y^2 + 6*y + 4) := by linarith only [h]
  have hw1 : 0 ≤ (-x^2 + 4*x - 9*y^2 - 6*y - 4) := by linarith only [h]
  have hsum : 0 ≤ (13 : ℝ) * (1) * (-7*x/26 + 6*y/13 + 1)^2 + (441/52 : ℝ) * (1) * (4*x/21 + y)^2 + (5/4 : ℝ) * ((-x^2 + 4*x - 9*y^2 - 6*y - 4)) * (1)^2 := by positivity
  have hid : ( 8  ) - ( (4*x - 9*y)/2 ) = (13 : ℝ) * (1) * (-7*x/26 + 6*y/13 + 1)^2 + (441/52 : ℝ) * (1) * (4*x/21 + y)^2 + (5/4 : ℝ) * ((-x^2 + 4*x - 9*y^2 - 6*y - 4)) * (1)^2 := by ring
  linarith only [hsum, hid]
theorem solution : (∀ x y : ℝ, x^2 + 9*y^2 - 4*x + 6*y + 4 = 0 → (4*x - 9*y)/2 ≤ 8) ∧ (∃ x y : ℝ, x^2 + 9*y^2 - 4*x + 6*y + 4 = 0 ∧ (4*x - 9*y)/2 = 8) := by
  constructor
  · intro x y h
    exact p2mUpperBound x y h
  · refine ⟨14/5, -8/15, ?_, ?_⟩ <;> norm_num
example : ((∀ x y : ℝ, x^2 + 9*y^2 - 4*x + 6*y + 4 = 0 → (4*x - 9*y)/2 ≤ 8) ∧ (∃ x y : ℝ, x^2 + 9*y^2 - 4*x + 6*y + 4 = 0 ∧ (4*x - 9*y)/2 = 8)) := @solution
#print axioms solution
