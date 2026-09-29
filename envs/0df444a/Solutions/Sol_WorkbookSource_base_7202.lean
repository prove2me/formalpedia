-- Prove2me | solution 1 for WorkbookSource.base_7202
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:28.691351+00:00
-- url     : https://prove2.me/submissions/8706cb1b-74fe-4845-a685-bc5672e38157

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) : (x + y + z) ^ 2 ≤ 2 * (1 + y * z) ^ 2  := by
  have hw0 : 0 ≤ (x) := by linarith only [hx]
  have hw1 : 0 ≤ (y) := by linarith only [hy]
  have hw2 : 0 ≤ (z) := by linarith only [hz]
  have hw3 : 0 ≤ (x^2 + y^2 + z^2 - 1) := by linarith only [h]
  have hw4 : 0 ≤ (-x^2 - y^2 - z^2 + 1) := by linarith only [h]
  have hsum : 0 ≤ (2 : ℝ) * (1) * (y*z)^2 + (1 : ℝ) * (1) * (-x + y + z)^2 + (2 : ℝ) * ((-x^2 - y^2 - z^2 + 1)) * (1)^2 := by positivity
  have hid : ( 2 * (1 + y * z) ^ 2  ) - ( (x + y + z) ^ 2 ) = (2 : ℝ) * (1) * (y*z)^2 + (1 : ℝ) * (1) * (-x + y + z)^2 + (2 : ℝ) * ((-x^2 - y^2 - z^2 + 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1), (x + y + z) ^ 2 ≤ 2 * (1 + y * z) ^ 2) := @solution
#print axioms solution
