-- Prove2me | solution 1 for WorkbookSource.base_3161
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:34:58.368481+00:00
-- url     : https://prove2.me/submissions/d04bd2e6-8f30-4bde-94ae-3c0ac6a8e515

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z > 1) : (1 / x + 1 / y + 1 / z + 1 / (x * y * z) - 4) * (1 / (x * y) + 1 / (y * z) + 1 / (z * x) - 3) ≥ 4 * (1 / (x * y * z) - 1) * (1 / x + 1 / y + 1 / z - 3)  := by
  have hn : 0 ≤ (x^2*y^2*z + x^2*y*z^2 - 4*x^2*y*z + x^2*y + x^2*z + x*y^2*z^2 - 4*x*y^2*z + x*y^2 - 4*x*y*z^2 + 12*x*y*z - 4*x*y + x*z^2 - 4*x*z + x + y^2*z + y*z^2 - 4*y*z + y + z) := by
    have hs0 : 0 ≤ (1 : ℝ) * (z) * (x*y - x - y + 1)^2 := by positivity
    have hs1 : 0 ≤ (1 : ℝ) * (y) * (x*z - x - z + 1)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (x) * (y*z - y - z + 1)^2 := by positivity
    nlinarith only [hs0, hs1, hs2]
  field_simp (disch := positivity)
  nlinarith only [hn]

example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z > 1), (1 / x + 1 / y + 1 / z + 1 / (x * y * z) - 4) * (1 / (x * y) + 1 / (y * z) + 1 / (z * x) - 3) ≥ 4 * (1 / (x * y * z) - 1) * (1 / x + 1 / y + 1 / z - 3)) := @solution
#print axioms solution
