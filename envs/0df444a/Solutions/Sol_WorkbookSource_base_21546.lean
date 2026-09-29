-- Prove2me | solution 1 for WorkbookSource.base_21546
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:41:02.47505+00:00
-- url     : https://prove2.me/submissions/a7cc4906-7bd8-417c-8f2a-934135c4fcf8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
  7 * (x ^ 4 + y ^ 4 + z ^ 4) + 8 * (x + y + z) * (x * y * z) ≥
  4 * (x * y + y * z + z * x) + 1  := by
  have hw0 : 0 ≤ (x^2 + y^2 + z^2 - 1) := by linarith only [hx]
  have hw1 : 0 ≤ (-x^2 - y^2 - z^2 + 1) := by linarith only [hx]
  have hsum : 0 ≤ (38/7 : ℝ) * (1) * (-9*x^2/19 + 17*x*y/38 - 11*x*z/38 - 9*y^2/19 - 11*y*z/38 + z^2 + 1/38)^2 + (80/19 : ℝ) * (1) * (-9*x^2/10 - x*y/10 + 2*x*z/5 + y^2 - 11*y*z/20 + 1/20)^2 + (61/70 : ℝ) * (1) * (-56*x^2/61 + x*y + x*z + 33*y*z/61 - 33/61)^2 + (4/61 : ℝ) * (1) * (x^2 + y*z/2 - 1/2)^2 + (11/7 : ℝ) * ((x^2 + y^2 + z^2 - 1)) * (x + y + z)^2 + (9/7 : ℝ) * ((x^2 + y^2 + z^2 - 1)) * (1)^2 := by positivity
  have hid : (
  7 * (x ^ 4 + y ^ 4 + z ^ 4) + 8 * (x + y + z) * (x * y * z) ) - (
  4 * (x * y + y * z + z * x) + 1  ) = (38/7 : ℝ) * (1) * (-9*x^2/19 + 17*x*y/38 - 11*x*z/38 - 9*y^2/19 - 11*y*z/38 + z^2 + 1/38)^2 + (80/19 : ℝ) * (1) * (-9*x^2/10 - x*y/10 + 2*x*z/5 + y^2 - 11*y*z/20 + 1/20)^2 + (61/70 : ℝ) * (1) * (-56*x^2/61 + x*y + x*z + 33*y*z/61 - 33/61)^2 + (4/61 : ℝ) * (1) * (x^2 + y*z/2 - 1/2)^2 + (11/7 : ℝ) * ((x^2 + y^2 + z^2 - 1)) * (x + y + z)^2 + (9/7 : ℝ) * ((x^2 + y^2 + z^2 - 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : x ^ 2 + y ^ 2 + z ^ 2 = 1), 7 * (x ^ 4 + y ^ 4 + z ^ 4) + 8 * (x + y + z) * (x * y * z) ≥
  4 * (x * y + y * z + z * x) + 1) := @solution
#print axioms solution
