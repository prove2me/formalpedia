-- Prove2me | solution 1 for WorkbookSource.base_12168
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:28.892597+00:00
-- url     : https://prove2.me/submissions/5a30ff8d-ea38-407b-9c2d-9f4926bd1e04

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x + y + z) ^ 4 ≥ (256 / 27) * (x ^ 3 * y + y ^ 3 * z + z ^ 3 * x) + (473 / 27) * (x + y + z) * x * y * z  := by
  have hn : 0 ≤ (27*x^4 - 148*x^3*y + 108*x^3*z + 162*x^2*y^2 - 149*x^2*y*z + 162*x^2*z^2 + 108*x*y^3 - 149*x*y^2*z - 149*x*y*z^2 - 148*x*z^3 + 27*y^4 - 148*y^3*z + 162*y^2*z^2 + 108*y*z^3 + 27*z^4) := by
    have hs0 : 0 ≤ (219 : ℝ) * (1) * (15*x^2/73 - x*y/2 - x*z/2 - 51*y^2/146 + y*z + 21*z^2/146)^2 := by positivity
    have hs1 : 0 ≤ (657/4 : ℝ) * (1) * (24*x^2/73 - x*y + x*z + 3*y^2/73 - 27*z^2/73)^2 := by positivity
    have hs2 : 0 ≤ (45 : ℝ) * (y*z) * (-2*x/3 - y/3 + z)^2 := by positivity
    have hs3 : 0 ≤ (45 : ℝ) * (x*z) * (x - 2*y/3 - z/3)^2 := by positivity
    have hs4 : 0 ≤ (45 : ℝ) * (x*y) * (-x/3 + y - 2*z/3)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0), (x + y + z) ^ 4 ≥ (256 / 27) * (x ^ 3 * y + y ^ 3 * z + z ^ 3 * x) + (473 / 27) * (x + y + z) * x * y * z) := @solution
#print axioms solution
