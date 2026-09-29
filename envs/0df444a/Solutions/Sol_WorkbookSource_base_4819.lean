-- Prove2me | solution 1 for WorkbookSource.base_4819
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:34:59.075961+00:00
-- url     : https://prove2.me/submissions/47286c13-3a76-4beb-82a2-f96832d67dc9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ 15 * (x + y + z) / (2 * (x ^ 2 + y ^ 2 + z ^ 2) + 8 * (x * y + y * z + z * x))  := by
  have hn : 0 ≤ (2*x^4 - x^3*y - x^3*z - 2*x^2*y^2 + 2*x^2*y*z - 2*x^2*z^2 - x*y^3 + 2*x*y^2*z + 2*x*y*z^2 - x*z^3 + 2*y^4 - y^3*z - 2*y^2*z^2 - y*z^3 + 2*z^4) := by
    have hs0 : 0 ≤ (2 : ℝ) * (1) * (-x^2/2 + x*y - x*z/2 - y^2/2 - y*z/2 + z^2)^2 := by positivity
    have hs1 : 0 ≤ (3/2 : ℝ) * (1) * (x^2 - x*z - y^2 + y*z)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (y*z) * (-y + z)^2 := by positivity
    have hs3 : 0 ≤ (1 : ℝ) * (x*z) * (-x + z)^2 := by positivity
    have hs4 : 0 ≤ (1 : ℝ) * (x*y) * (-x + y)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  field_simp (disch := positivity)
  nlinarith only [hn]

example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (1 / (x + y) + 1 / (y + z) + 1 / (z + x)) ≥ 15 * (x + y + z) / (2 * (x ^ 2 + y ^ 2 + z ^ 2) + 8 * (x * y + y * z + z * x))) := @solution
#print axioms solution
