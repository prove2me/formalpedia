-- Prove2me | solution 1 for WorkbookSource.base_13426
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:41:01.868258+00:00
-- url     : https://prove2.me/submissions/cb08ae81-61f4-4e5b-9165-9432fe4b1180

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a^2 + b^2 + c^2 = 4) : a^4 + b^4 + c^4 + 6 * (a * b + b * c + c * a) ≤ 30  := by
  have hw0 : 0 ≤ (a^2 + b^2 + c^2 - 4) := by linarith only [h]
  have hw1 : 0 ≤ (-a^2 - b^2 - c^2 + 4) := by linarith only [h]
  have hsum : 0 ≤ (2 : ℝ) * (1) * (-a^2/4 - b^2/4 + b*c - c^2/4 - 1/2)^2 + (2 : ℝ) * (1) * (-a^2/4 + a*c - b^2/4 - c^2/4 - 1/2)^2 + (2 : ℝ) * (1) * (-a^2/4 + a*b - b^2/4 - c^2/4 - 1/2)^2 + (1/18 : ℝ) * (1) * (a^2/10 + b^2/10 + c^2/10 + 1)^2 + (11/450 : ℝ) * (1) * (a^2 + b^2 + c^2)^2 + (64/9 : ℝ) * ((-a^2 - b^2 - c^2 + 4)) * (1)^2 + (7/5 : ℝ) * ((-a^2 - b^2 - c^2 + 4)) * (-5*a/14 - 5*b/14 + c)^2 + (171/140 : ℝ) * ((-a^2 - b^2 - c^2 + 4)) * (-5*a/9 + b)^2 + (38/45 : ℝ) * ((-a^2 - b^2 - c^2 + 4)) * (a)^2 := by positivity
  have hid : ( 30  ) - ( a^4 + b^4 + c^4 + 6 * (a * b + b * c + c * a) ) = (2 : ℝ) * (1) * (-a^2/4 - b^2/4 + b*c - c^2/4 - 1/2)^2 + (2 : ℝ) * (1) * (-a^2/4 + a*c - b^2/4 - c^2/4 - 1/2)^2 + (2 : ℝ) * (1) * (-a^2/4 + a*b - b^2/4 - c^2/4 - 1/2)^2 + (1/18 : ℝ) * (1) * (a^2/10 + b^2/10 + c^2/10 + 1)^2 + (11/450 : ℝ) * (1) * (a^2 + b^2 + c^2)^2 + (64/9 : ℝ) * ((-a^2 - b^2 - c^2 + 4)) * (1)^2 + (7/5 : ℝ) * ((-a^2 - b^2 - c^2 + 4)) * (-5*a/14 - 5*b/14 + c)^2 + (171/140 : ℝ) * ((-a^2 - b^2 - c^2 + 4)) * (-5*a/9 + b)^2 + (38/45 : ℝ) * ((-a^2 - b^2 - c^2 + 4)) * (a)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a^2 + b^2 + c^2 = 4), a^4 + b^4 + c^4 + 6 * (a * b + b * c + c * a) ≤ 30) := @solution
#print axioms solution
