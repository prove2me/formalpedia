-- Prove2me | solution 1 for WorkbookSource.base_7020
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:36.657565+00:00
-- url     : https://prove2.me/submissions/617cadc9-2bae-44e8-a27f-cd28257dd58e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : x * (y + z - x) ^ 2 + y * (x + z - y) ^ 2 + z * (x + y - z) ^ 2 ≥ 2 * x * y * z * (x/(y+z) + y/(x+z) + z/(x+y))  := by
  have hn : 0 ≤ (x^5*y + x^5*z - 2*x^4*y*z - 2*x^3*y^3 + x^3*y^2*z + x^3*y*z^2 - 2*x^3*z^3 + x^2*y^3*z + x^2*y*z^3 + x*y^5 - 2*x*y^4*z + x*y^3*z^2 + x*y^2*z^3 - 2*x*y*z^4 + x*z^5 + y^5*z - 2*y^3*z^3 + y*z^5) := by
    have hs0 : 0 ≤ (1/2 : ℝ) * (1) * (x^2*y/2 - x^2*z/2 - x*y^2/2 + x*z^2/2 - y^2*z + y*z^2)^2 := by positivity
    have hs1 : 0 ≤ (3/8 : ℝ) * (1) * (-x^2*y - x^2*z + x*y^2 + x*z^2)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (y*z) * (-x^2/4 + x*y - 3*x*z/4 - 3*y^2/4 - y*z/4 + z^2)^2 := by positivity
    have hs3 : 0 ≤ (7/16 : ℝ) * (y*z) * (x^2 - x*z - y^2 + y*z)^2 := by positivity
    have hs4 : 0 ≤ (1 : ℝ) * (x*z) * (-3*x^2/4 + x*y - x*z/4 - y^2/4 - 3*y*z/4 + z^2)^2 := by positivity
    have hs5 : 0 ≤ (7/16 : ℝ) * (x*z) * (x^2 - x*z - y^2 + y*z)^2 := by positivity
    have hs6 : 0 ≤ (1 : ℝ) * (x*y) * (x^2 - x*y/4 - 3*x*z/4 - 3*y^2/4 + y*z - z^2/4)^2 := by positivity
    have hs7 : 0 ≤ (7/16 : ℝ) * (x*y) * (x*y - x*z - y^2 + z^2)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7]
  field_simp (disch := positivity)
  nlinarith only [hn]

example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), x * (y + z - x) ^ 2 + y * (x + z - y) ^ 2 + z * (x + y - z) ^ 2 ≥ 2 * x * y * z * (x/(y+z) + y/(x+z) + z/(x+y))) := @solution
#print axioms solution
