-- Prove2me | solution 1 for WorkbookSource.base_15913
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:36.291684+00:00
-- url     : https://prove2.me/submissions/857edbd7-a320-4e59-87c9-b6b5a517284a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y + z) ^ 2 / x ^ 2 + (z + x) ^ 2 / y ^ 2 + (x + y) ^ 2 / z ^ 2 + 28 ≥ 5 * (x + y) * (y + z) * (z + x) / (x * y * z)  := by
  have hn : 0 ≤ (x^4*y^2 + x^4*z^2 + 2*x^3*y^3 - 5*x^3*y^2*z - 5*x^3*y*z^2 + 2*x^3*z^3 + x^2*y^4 - 5*x^2*y^3*z + 18*x^2*y^2*z^2 - 5*x^2*y*z^3 + x^2*z^4 - 5*x*y^3*z^2 - 5*x*y^2*z^3 + y^4*z^2 + 2*y^3*z^3 + y^2*z^4) := by
    have hs0 : 0 ≤ (12 : ℝ) * (1) * (-x^2*y/6 - x^2*z/6 - x*y^2/6 + x*y*z - x*z^2/6 - y^2*z/6 - y*z^2/6)^2 := by positivity
    have hs1 : 0 ≤ (2/3 : ℝ) * (1) * (-x^2*z/2 - x*y^2/2 - 3*x*z^2/4 + 3*y^2*z/4 + y*z^2)^2 := by positivity
    have hs2 : 0 ≤ (2/3 : ℝ) * (1) * (x^2*y - 3*x^2*z/4 + 3*x*y^2/4 - x*z^2/2 - y^2*z/2)^2 := by positivity
    have hs3 : 0 ≤ (1/8 : ℝ) * (1) * (-x*z^2 + y^2*z)^2 := by positivity
    have hs4 : 0 ≤ (1/8 : ℝ) * (1) * (-x^2*z + x*y^2)^2 := by positivity
    have hs5 : 0 ≤ (1/3 : ℝ) * (y*z) * (x^2 - x*y - x*z + y*z)^2 := by positivity
    have hs6 : 0 ≤ (1/3 : ℝ) * (x*z) * (x*y - x*z - y^2 + y*z)^2 := by positivity
    have hs7 : 0 ≤ (1/3 : ℝ) * (x*y) * (x*y - x*z - y*z + z^2)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (y + z) ^ 2 / x ^ 2 + (z + x) ^ 2 / y ^ 2 + (x + y) ^ 2 / z ^ 2 + 28 ≥ 5 * (x + y) * (y + z) * (z + x) / (x * y * z)) := @solution
#print axioms solution
