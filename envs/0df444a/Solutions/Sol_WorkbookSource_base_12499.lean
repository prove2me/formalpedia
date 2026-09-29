-- Prove2me | solution 1 for WorkbookSource.base_12499
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:13:47.211857+00:00
-- url     : https://prove2.me/submissions/06b13cb6-aa45-4e60-95c5-6f412c6ed11d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) = 64) :
 a * b + b * c + c * a ≤ 9  := by
  have hw0 : 0 ≤ (a^2*b^2*c^2 + a^2*b^2 + a^2*c^2 + a^2 + b^2*c^2 + b^2 + c^2 - 63) := by linarith only [h]
  have hw1 : 0 ≤ (-a^2*b^2*c^2 - a^2*b^2 - a^2*c^2 - a^2 - b^2*c^2 - b^2 - c^2 + 63) := by linarith only [h]
  have hsum : 0 ≤ (81/16 : ℝ) * (1) * (-a*b/9 - a*c/9 - b*c/9 + 1)^2 + (1/16 : ℝ) * (1) * (-a*b*c + a + b + c)^2 + (1/16 : ℝ) * ((-a^2*b^2*c^2 - a^2*b^2 - a^2*c^2 - a^2 - b^2*c^2 - b^2 - c^2 + 63)) * (1)^2 := by positivity
  have hid : ( 9  ) - (
 a * b + b * c + c * a ) = (81/16 : ℝ) * (1) * (-a*b/9 - a*c/9 - b*c/9 + 1)^2 + (1/16 : ℝ) * (1) * (-a*b*c + a + b + c)^2 + (1/16 : ℝ) * ((-a^2*b^2*c^2 - a^2*b^2 - a^2*c^2 - a^2 - b^2*c^2 - b^2 - c^2 + 63)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : (a^2 + 1) * (b^2 + 1) * (c^2 + 1) = 64), a * b + b * c + c * a ≤ 9) := @solution
#print axioms solution
