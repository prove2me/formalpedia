-- Prove2me | solution 1 for WorkbookSource.base_23054
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:55:40.632683+00:00
-- url     : https://prove2.me/submissions/5867408b-5b82-42c5-92f3-de4574e79e64

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x + y + z) ^ 6 ≥ (8 * x ^ 2 + y * z) * (8 * y ^ 2 + x * z) * (8 * z ^ 2 + x * y)  := by
  have h0 : 0 ≤ (16 : ℝ) * (1) * (x^3/32 - 31*x^2*y/32 + 31*x^2*z/32 + 31*x*y^2/32 - x*z^2 - y^3/32 - 31*y^2*z/32 + y*z^2)^2 := by positivity
  have h1 : 0 ≤ (1 : ℝ) * (1) * (-x^3/2 + x^2*y/2 - x^2*z/2 + x*y^2/2 - y^3/2 - y^2*z/2 + z^3)^2 := by positivity
  have h2 : 0 ≤ (47/64 : ℝ) * (1) * (x^3 + x^2*y - x^2*z - x*y^2 - y^3 + y^2*z)^2 := by positivity
  have h3 : 0 ≤ (55 : ℝ) * (y*z) * (-x*y + x*z - 27*y^2/110 + 27*z^2/110)^2 := by positivity
  have h4 : 0 ≤ (591/220 : ℝ) * (y*z) * (-y^2 + z^2)^2 := by positivity
  have h5 : 0 ≤ (55 : ℝ) * (x*z) * (-27*x^2/110 - x*y + y*z + 27*z^2/110)^2 := by positivity
  have h6 : 0 ≤ (591/220 : ℝ) * (x*z) * (-x^2 + z^2)^2 := by positivity
  have h7 : 0 ≤ (55 : ℝ) * (x*y) * (-27*x^2/110 - x*z + 27*y^2/110 + y*z)^2 := by positivity
  have h8 : 0 ≤ (591/220 : ℝ) * (x*y) * (-x^2 + y^2)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), (x + y + z) ^ 6 ≥ (8 * x ^ 2 + y * z) * (8 * y ^ 2 + x * z) * (8 * z ^ 2 + x * y)) := @solution
#print axioms solution
