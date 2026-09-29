-- Prove2me | solution 1 for WorkbookSource.base_747
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:11:08.313891+00:00
-- url     : https://prove2.me/submissions/16d2b222-5a02-4300-837e-db40cb147bef

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a^2 + b^2 + c^2 = 1) : (a + b + c) * (a^3 + b^3 + c^3) ≤ 5 / 4  := by
  have hw0 : 0 ≤ (a^2 + b^2 + c^2 - 1) := by linarith only [h]
  have hw1 : 0 ≤ (-a^2 - b^2 - c^2 + 1) := by linarith only [h]
  have hsum : 0 ≤ (2 : ℝ) * (1) * (-a^2/20 + a*b/4 + a*c/4 - b^2/20 + b*c - c^2/20 - 1/5)^2 + (15/8 : ℝ) * (1) * (-a^2/25 + a*b/5 + a*c - b^2/25 - c^2/25 - 4/25)^2 + (9/5 : ℝ) * (1) * (-a^2/30 + a*b - b^2/30 - c^2/30 - 2/15)^2 + (3/200 : ℝ) * (1) * (-a^2 - b^2 - c^2 + 1)^2 + (17/10 : ℝ) * ((-a^2 - b^2 - c^2 + 1)) * (1)^2 + (2/5 : ℝ) * ((-a^2 - b^2 - c^2 + 1)) * (a + b + c)^2 + (5/8 : ℝ) * ((a^2 + b^2 + c^2 - 1) * (-a^2 - b^2 - c^2 + 1)) * (1)^2 := by positivity
  have hid : ( 5 / 4  ) - ( (a + b + c) * (a^3 + b^3 + c^3) ) = (2 : ℝ) * (1) * (-a^2/20 + a*b/4 + a*c/4 - b^2/20 + b*c - c^2/20 - 1/5)^2 + (15/8 : ℝ) * (1) * (-a^2/25 + a*b/5 + a*c - b^2/25 - c^2/25 - 4/25)^2 + (9/5 : ℝ) * (1) * (-a^2/30 + a*b - b^2/30 - c^2/30 - 2/15)^2 + (3/200 : ℝ) * (1) * (-a^2 - b^2 - c^2 + 1)^2 + (17/10 : ℝ) * ((-a^2 - b^2 - c^2 + 1)) * (1)^2 + (2/5 : ℝ) * ((-a^2 - b^2 - c^2 + 1)) * (a + b + c)^2 + (5/8 : ℝ) * ((a^2 + b^2 + c^2 - 1) * (-a^2 - b^2 - c^2 + 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a^2 + b^2 + c^2 = 1), (a + b + c) * (a^3 + b^3 + c^3) ≤ 5 / 4) := @solution
#print axioms solution
