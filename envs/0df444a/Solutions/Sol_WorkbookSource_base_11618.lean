-- Prove2me | solution 1 for WorkbookSource.base_11618
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:47.751933+00:00
-- url     : https://prove2.me/submissions/92b87d61-77d6-47d7-a93a-3de1baf44890

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 12 * (x * y + y * z + z * x) / (x + y + z) ^ 2 + 2 * (x / (y + z) + y / (x + z) + z / (x + y)) ≥ 7  := by
  have hn : 0 ≤ (2*x^5 - x^4*y - x^4*z - x^3*y^2 - x^3*z^2 - x^2*y^3 + 2*x^2*y^2*z + 2*x^2*y*z^2 - x^2*z^3 - x*y^4 + 2*x*y^2*z^2 - x*z^4 + 2*y^5 - y^4*z - y^3*z^2 - y^2*z^3 - y*z^4 + 2*z^5) := by
    have hs0 : 0 ≤ (2 : ℝ) * (z) * (-x^2/2 + x*y - x*z/2 - y^2/2 - y*z/2 + z^2)^2 := by positivity
    have hs1 : 0 ≤ (1/2 : ℝ) * (z) * (x^2 - x*z - y^2 + y*z)^2 := by positivity
    have hs2 : 0 ≤ (2 : ℝ) * (y) * (-x^2/2 - x*y/2 + x*z + y^2 - y*z/2 - z^2/2)^2 := by positivity
    have hs3 : 0 ≤ (1/2 : ℝ) * (y) * (-x^2 + x*y - y*z + z^2)^2 := by positivity
    have hs4 : 0 ≤ (2 : ℝ) * (x) * (x^2 - x*y/2 - x*z/2 - y^2/2 + y*z - z^2/2)^2 := by positivity
    have hs5 : 0 ≤ (1/2 : ℝ) * (x) * (x*y - x*z - y^2 + z^2)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), 12 * (x * y + y * z + z * x) / (x + y + z) ^ 2 + 2 * (x / (y + z) + y / (x + z) + z / (x + y)) ≥ 7) := @solution
#print axioms solution
