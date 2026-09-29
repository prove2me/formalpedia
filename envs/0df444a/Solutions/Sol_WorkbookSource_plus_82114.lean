-- Prove2me | solution 1 for WorkbookSource.plus_82114
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:51.834511+00:00
-- url     : https://prove2.me/submissions/ef2a244d-19c4-44be-94b3-3466b52582ca

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 3 * (x^2 * y + y^2 * z + z^2 * x) * (x * y^2 + y * z^2 + x^2 * z) ≥ (x * y + y * z + z * x)^3   := by
  have h0 : 0 ≤ (3 : ℝ) * (y*z) * (x^2 - 5*x*y/12 - 5*x*z/12 - y*z/6)^2 := by positivity
  have h1 : 0 ≤ (23/12 : ℝ) * (y*z) * (-x*y/2 - x*z/2 + y*z)^2 := by positivity
  have h2 : 0 ≤ (3 : ℝ) * (x*z) * (-5*x*y/12 - x*z/6 + y^2 - 5*y*z/12)^2 := by positivity
  have h3 : 0 ≤ (23/12 : ℝ) * (x*z) * (-x*y/2 + x*z - y*z/2)^2 := by positivity
  have h4 : 0 ≤ (3 : ℝ) * (x*y) * (-x*y/6 - 5*x*z/12 - 5*y*z/12 + z^2)^2 := by positivity
  have h5 : 0 ≤ (23/12 : ℝ) * (x*y) * (x*y - x*z/2 - y*z/2)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4, h5]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 3 * (x^2 * y + y^2 * z + z^2 * x) * (x * y^2 + y * z^2 + x^2 * z) ≥ (x * y + y * z + z * x)^3) := @solution
#print axioms solution
