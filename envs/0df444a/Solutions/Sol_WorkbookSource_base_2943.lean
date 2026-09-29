-- Prove2me | solution 1 for WorkbookSource.base_2943
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:41:00.516331+00:00
-- url     : https://prove2.me/submissions/9e02411f-aa03-4f96-a1f3-8801a2fe57f7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 = 2) :
  a * b + b * c + c * a ≤ 1 + a * b * c * (a + b + c)  := by
  have hw0 : 0 ≤ (a^2 + b^2 + c^2 - 2) := by linarith only [h]
  have hw1 : 0 ≤ (-a^2 - b^2 - c^2 + 2) := by linarith only [h]
  have hsum : 0 ≤ (1/2 : ℝ) * (1) * (a^2/3 + a*b/2 + a*c/2 - b^2/6 + b*c - c^2/6 - 2/3)^2 + (3/8 : ℝ) * (1) * (-4*a^2/9 + a*b/3 + a*c + 5*b^2/9 - c^2/9 - 4/9)^2 + (1/3 : ℝ) * (1) * (-a^2/3 + a*b - b^2/3 + 2*c^2/3 - 1/3)^2 + (1/3 : ℝ) * ((-a^2 - b^2 - c^2 + 2)) * (1)^2 + (1/6 : ℝ) * ((-a^2 - b^2 - c^2 + 2)) * (-a/2 - b/2 + c)^2 + (1/8 : ℝ) * ((-a^2 - b^2 - c^2 + 2)) * (-a + b)^2 := by positivity
  have hid : ( 1 + a * b * c * (a + b + c)  ) - (
  a * b + b * c + c * a ) = (1/2 : ℝ) * (1) * (a^2/3 + a*b/2 + a*c/2 - b^2/6 + b*c - c^2/6 - 2/3)^2 + (3/8 : ℝ) * (1) * (-4*a^2/9 + a*b/3 + a*c + 5*b^2/9 - c^2/9 - 4/9)^2 + (1/3 : ℝ) * (1) * (-a^2/3 + a*b - b^2/3 + 2*c^2/3 - 1/3)^2 + (1/3 : ℝ) * ((-a^2 - b^2 - c^2 + 2)) * (1)^2 + (1/6 : ℝ) * ((-a^2 - b^2 - c^2 + 2)) * (-a/2 - b/2 + c)^2 + (1/8 : ℝ) * ((-a^2 - b^2 - c^2 + 2)) * (-a + b)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a ^ 2 + b ^ 2 + c ^ 2 = 2), a * b + b * c + c * a ≤ 1 + a * b * c * (a + b + c)) := @solution
#print axioms solution
