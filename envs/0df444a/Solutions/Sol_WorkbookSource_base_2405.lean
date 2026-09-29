-- Prove2me | solution 1 for WorkbookSource.base_2405
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T23:04:09.183738+00:00
-- url     : https://prove2.me/submissions/6534133e-421b-420a-b582-e2214aa9e0f3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : x ^ 4 + y ^ 4 + z ^ 4 + x * y * z * (x + y + z) ≥ 2 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2)  := by
  have h0 : 0 ≤ (1 : ℝ) * (1) * (-x^2/2 + x*y - x*z/2 - y^2/2 - y*z/2 + z^2)^2 := by positivity
  have h1 : 0 ≤ (3/4 : ℝ) * (1) * (x^2 - x*z - y^2 + y*z)^2 := by positivity
  have h2 : 0 ≤ (1 : ℝ) * (y*z) * (-y + z)^2 := by positivity
  have h3 : 0 ≤ (1 : ℝ) * (x*z) * (-x + z)^2 := by positivity
  have h4 : 0 ≤ (1 : ℝ) * (x*y) * (-x + y)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0), x ^ 4 + y ^ 4 + z ^ 4 + x * y * z * (x + y + z) ≥ 2 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2)) := @solution
#print axioms solution
