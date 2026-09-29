-- Prove2me | solution 1 for WorkbookSource.base_18503
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:54:45.24566+00:00
-- url     : https://prove2.me/submissions/a2efbc88-785a-49d7-af64-51e8741acf59

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (z / (2 * x + y) + x / (2 * y + z) + y / (2 * z + x)) ≥ 1 / 3 * (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x) + 2 / 3  := by
  have hn : 0 ≤ (2*x^4*y + 4*x^4*z - 7*x^3*y^2 + 4*x^3*z^2 + 4*x^2*y^3 - 3*x^2*y^2*z - 3*x^2*y*z^2 - 7*x^2*z^3 + 4*x*y^4 - 3*x*y^2*z^2 + 2*x*z^4 + 2*y^4*z - 7*y^3*z^2 + 4*y^2*z^3 + 4*y*z^4) := by
    have hs0 : 0 ≤ (8 : ℝ) * (z) * (-x*y/2 - y^2/2 + y*z)^2 := by positivity
    have hs1 : 0 ≤ (4 : ℝ) * (z) * (x^2 - x*y/2 - x*z/2)^2 := by positivity
    have hs2 : 0 ≤ (8 : ℝ) * (y) * (-x^2/2 + x*y - x*z/2)^2 := by positivity
    have hs3 : 0 ≤ (4 : ℝ) * (y) * (-x*z/2 - y*z/2 + z^2)^2 := by positivity
    have hs4 : 0 ≤ (8 : ℝ) * (x) * (x*z - y*z/2 - z^2/2)^2 := by positivity
    have hs5 : 0 ≤ (4 : ℝ) * (x) * (-x*y/2 + y^2 - y*z/2)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (z / (2 * x + y) + x / (2 * y + z) + y / (2 * z + x)) ≥ 1 / 3 * (x ^ 2 + y ^ 2 + z ^ 2) / (x * y + y * z + z * x) + 2 / 3) := @solution
#print axioms solution
