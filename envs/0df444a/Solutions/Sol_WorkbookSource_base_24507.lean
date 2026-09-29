-- Prove2me | solution 1 for WorkbookSource.base_24507
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:45:20.652333+00:00
-- url     : https://prove2.me/submissions/bc09e5f7-189d-41f0-bd88-cdfda18c0c50

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a^2 + a * b + b^2 = 3) (hb : b^2 + b * c + c^2 = 16) : a * b + b * c + c * a ≤ 8  := by
  have hw0 : 0 ≤ (a^2 + a*b + b^2 - 3) := by linarith only [ha]
  have hw1 : 0 ≤ (-a^2 - a*b - b^2 + 3) := by linarith only [ha]
  have hw2 : 0 ≤ (b^2 + b*c + c^2 - 16) := by linarith only [hb]
  have hw3 : 0 ≤ (-b^2 - b*c - c^2 + 16) := by linarith only [hb]
  have hsum : 0 ≤ (19/12 : ℝ) * (1) * (2*a/19 + b - 9*c/38)^2 + (25/19 : ℝ) * (1) * (a - 7*c/20)^2 + (1/4 : ℝ) * ((-b^2 - b*c - c^2 + 16)) * (1)^2 + (4/3 : ℝ) * ((-a^2 - a*b - b^2 + 3)) * (1)^2 := by positivity
  have hid : ( 8  ) - ( a * b + b * c + c * a ) = (19/12 : ℝ) * (1) * (2*a/19 + b - 9*c/38)^2 + (25/19 : ℝ) * (1) * (a - 7*c/20)^2 + (1/4 : ℝ) * ((-b^2 - b*c - c^2 + 16)) * (1)^2 + (4/3 : ℝ) * ((-a^2 - a*b - b^2 + 3)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a^2 + a * b + b^2 = 3) (hb : b^2 + b * c + c^2 = 16), a * b + b * c + c * a ≤ 8) := @solution
#print axioms solution
