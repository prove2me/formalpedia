-- Prove2me | solution 1 for WorkbookSource.base_7325
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:11:11.124808+00:00
-- url     : https://prove2.me/submissions/27735a9f-8590-4ce3-b717-a16408a62a58

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d e : ℝ) (h : a + b + c + d + e = 1) :  2 * (a * b + b * c + c * d + d * e + e * a) + a * c + b * d + c * e + d * a + e * b ≤ 3 / 5  := by
  have hw0 : 0 ≤ (a + b + c + d + e - 1) := by linarith only [h]
  have hw1 : 0 ≤ (-a - b - c - d - e + 1) := by linarith only [h]
  have hsum : 0 ≤ (3/5 : ℝ) * (1) * (-2*a/3 + b/6 + c/6 - 2*d/3 + e)^2 + (7/12 : ℝ) * (1) * (2*a/7 - 5*b/7 + c - 4*d/7)^2 + (2/7 : ℝ) * (1) * (-3*a/4 + b - d/4)^2 + (1/8 : ℝ) * (1) * (-a + d)^2 + (6/5 : ℝ) * ((-a - b - c - d - e + 1)) * (1)^2 + (3/5 : ℝ) * ((a + b + c + d + e - 1) * (-a - b - c - d - e + 1)) * (1)^2 := by positivity
  have hid : ( 3 / 5  ) - (  2 * (a * b + b * c + c * d + d * e + e * a) + a * c + b * d + c * e + d * a + e * b ) = (3/5 : ℝ) * (1) * (-2*a/3 + b/6 + c/6 - 2*d/3 + e)^2 + (7/12 : ℝ) * (1) * (2*a/7 - 5*b/7 + c - 4*d/7)^2 + (2/7 : ℝ) * (1) * (-3*a/4 + b - d/4)^2 + (1/8 : ℝ) * (1) * (-a + d)^2 + (6/5 : ℝ) * ((-a - b - c - d - e + 1)) * (1)^2 + (3/5 : ℝ) * ((a + b + c + d + e - 1) * (-a - b - c - d - e + 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d e : ℝ) (h : a + b + c + d + e = 1), 2 * (a * b + b * c + c * d + d * e + e * a) + a * c + b * d + c * e + d * a + e * b ≤ 3 / 5) := @solution
#print axioms solution
