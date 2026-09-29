-- Prove2me | solution 1 for WorkbookSource.base_13913
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:32.897644+00:00
-- url     : https://prove2.me/submissions/3cf643b9-87f1-4a7d-a86b-eaf6cd4cc5bc

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (9 / 2 * (x + y) * (z + x) * (y + z) / ((x + y + z) * (x * y + x * z + y * z))) ≥ (y + z) / (2 * x + z + y) + (z + x) / (2 * y + x + z) + (x + y) / (2 * z + y + x) + 5 / 2  := by
  have hn : 0 ≤ (6*x^4*y^2 - 6*x^4*y*z + 6*x^4*z^2 + 12*x^3*y^3 - 5*x^3*y^2*z - 5*x^3*y*z^2 + 12*x^3*z^3 + 6*x^2*y^4 - 5*x^2*y^3*z - 24*x^2*y^2*z^2 - 5*x^2*y*z^3 + 6*x^2*z^4 - 6*x*y^4*z - 5*x*y^3*z^2 - 5*x*y^2*z^3 - 6*x*y*z^4 + 6*y^4*z^2 + 12*y^3*z^3 + 6*y^2*z^4) := by
    have hs0 : 0 ≤ (6 : ℝ) * (1) * (-x^2*y/2 - x^2*z/2 - x*y^2/2 - x*z^2/2 + y^2*z + y*z^2)^2 := by positivity
    have hs1 : 0 ≤ (9/2 : ℝ) * (1) * (-x^2*y + x^2*z - x*y^2 + x*z^2)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (y*z) * (-x*y + x*z)^2 := by positivity
    have hs3 : 0 ≤ (1 : ℝ) * (x*z) * (-x*y + y*z)^2 := by positivity
    have hs4 : 0 ≤ (1 : ℝ) * (x*y) * (-x*z + y*z)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (9 / 2 * (x + y) * (z + x) * (y + z) / ((x + y + z) * (x * y + x * z + y * z))) ≥ (y + z) / (2 * x + z + y) + (z + x) / (2 * y + x + z) + (x + y) / (2 * z + y + x) + 5 / 2) := @solution
#print axioms solution
