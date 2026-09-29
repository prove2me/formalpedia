-- Prove2me | solution 1 for WorkbookSource.base_6442
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:27.939989+00:00
-- url     : https://prove2.me/submissions/e9b039d9-5625-461b-97bc-eb2f808fc9ff

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : 2 * (a^2 - a + 1) * (b^2 - b + 1) * (c^2 - c + 1) ≥ (a * b * c - 1)^2  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hsum : 0 ≤ (2 : ℝ) * (1) * (a*b*c/6 - a*c/2 + a/3 - b*c/2 + b/3 + c - 1/2)^2 + (2 : ℝ) * (1) * (-a*b*c/2 + a*b + a*c/3 - a/2 + b*c/3 - b/2 + 1/6)^2 + (23/18 : ℝ) * (1) * (-5*a*b*c/23 + 12*a*c/23 - a/23 - 6*b*c/23 + b - 9/23)^2 + (88/69 : ℝ) * (1) * (-5*a*b*c/22 - 21*a*c/88 + a + 45*b*c/88 - 9/22)^2 + (679/792 : ℝ) * (1) * (-48*a*b*c/97 + 31*a*c/97 + b*c - 16/97)^2 + (224/291 : ℝ) * (1) * (-3*a*b*c/8 + a*c - 1/8)^2 := by positivity
  have hid : ( 2 * (a^2 - a + 1) * (b^2 - b + 1) * (c^2 - c + 1) ) - ( (a * b * c - 1)^2  ) = (2 : ℝ) * (1) * (a*b*c/6 - a*c/2 + a/3 - b*c/2 + b/3 + c - 1/2)^2 + (2 : ℝ) * (1) * (-a*b*c/2 + a*b + a*c/3 - a/2 + b*c/3 - b/2 + 1/6)^2 + (23/18 : ℝ) * (1) * (-5*a*b*c/23 + 12*a*c/23 - a/23 - 6*b*c/23 + b - 9/23)^2 + (88/69 : ℝ) * (1) * (-5*a*b*c/22 - 21*a*c/88 + a + 45*b*c/88 - 9/22)^2 + (679/792 : ℝ) * (1) * (-48*a*b*c/97 + 31*a*c/97 + b*c - 16/97)^2 + (224/291 : ℝ) * (1) * (-3*a*b*c/8 + a*c - 1/8)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0), 2 * (a^2 - a + 1) * (b^2 - b + 1) * (c^2 - c + 1) ≥ (a * b * c - 1)^2) := @solution
#print axioms solution
