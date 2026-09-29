-- Prove2me | solution 1 for WorkbookSource.base_13763
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:31.878996+00:00
-- url     : https://prove2.me/submissions/869c44e1-5531-4eb9-9273-5475467fc362

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x / (x + 2) + y / (y + 2) + z / (z + 2)) ≥ (x + y + z) ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2 + 2 * x + 2 * y + 2 * z)  := by
  have hn : 0 ≤ (2*x^3*y*z + 2*x^3*y + 2*x^3*z - 2*x^2*y^2*z - 4*x^2*y^2 - 2*x^2*y*z^2 - 4*x^2*z^2 + 2*x*y^3*z + 2*x*y^3 - 2*x*y^2*z^2 + 2*x*y*z^3 + 2*x*z^3 + 2*y^3*z - 4*y^2*z^2 + 2*y*z^3) := by
    have hs0 : 0 ≤ (2 : ℝ) * (y*z) * (-y + z)^2 := by positivity
    have hs1 : 0 ≤ (2 : ℝ) * (x*z) * (-x + z)^2 := by positivity
    have hs2 : 0 ≤ (2 : ℝ) * (x*y) * (-x + y)^2 := by positivity
    have hs3 : 0 ≤ (2 : ℝ) * (x*y*z) * (-x/2 - y/2 + z)^2 := by positivity
    have hs4 : 0 ≤ (3/2 : ℝ) * (x*y*z) * (-x + y)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0), (x / (x + 2) + y / (y + 2) + z / (z + 2)) ≥ (x + y + z) ^ 2 / (x ^ 2 + y ^ 2 + z ^ 2 + 2 * x + 2 * y + 2 * z)) := @solution
#print axioms solution
