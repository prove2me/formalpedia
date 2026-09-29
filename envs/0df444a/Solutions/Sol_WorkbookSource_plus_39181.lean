-- Prove2me | solution 1 for WorkbookSource.plus_39181
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:47.643158+00:00
-- url     : https://prove2.me/submissions/04f05aee-4d11-4f2a-bf1f-92b8c68a78aa

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 + y^2 + z^2)^3 ≥ 8 * (x^3 * y^3 + y^3 * z^3 + z^3 * x^3) + 12 * (x - y)^2 * (y - z)^2 * (z - x)^2   := by
  have h0 : 0 ≤ (12 : ℝ) * (1) * (x^3/4 - x^2*y/4 - x^2*z/4 - x*y^2/4 + x*y*z - x*z^2/4 + y^3/4 - y^2*z/4 - y*z^2/4 + z^3/4)^2 := by positivity
  have h1 : 0 ≤ (1/4 : ℝ) * (1) * (x^3 - x^2*y - x^2*z - x*y^2 - x*z^2 + y^3 - y^2*z - y*z^2 + z^3)^2 := by positivity
  have h2 : 0 ≤ (8 : ℝ) * (y*z) * (x^2 - x*y/2 - x*z/2 - y^2/2 + y*z - z^2/2)^2 := by positivity
  have h3 : 0 ≤ (8 : ℝ) * (x*z) * (-x^2/2 - x*y/2 + x*z + y^2 - y*z/2 - z^2/2)^2 := by positivity
  have h4 : 0 ≤ (8 : ℝ) * (x*y) * (-x^2/2 + x*y - x*z/2 - y^2/2 - y*z/2 + z^2)^2 := by positivity
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x^2 + y^2 + z^2)^3 ≥ 8 * (x^3 * y^3 + y^3 * z^3 + z^3 * x^3) + 12 * (x - y)^2 * (y - z)^2 * (z - x)^2) := @solution
#print axioms solution
