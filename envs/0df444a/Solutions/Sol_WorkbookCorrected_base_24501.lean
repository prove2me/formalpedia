-- Prove2me | solution 1 for WorkbookCorrected.base_24501
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:29:29.033302+00:00
-- url     : https://prove2.me/submissions/2817b181-c90b-49e5-8f73-513808b31392

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : -(x * y + x * z + y * z) ^ 2 * (x * y ^ 3 + y * z ^ 3 + x ^ 3 * z) + (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 * z ^ 3 + x ^ 3 * y ^ 2 + y ^ 3 * z ^ 2) ≥ 0  := by
  have hsum : 0 ≤ (1 : ℝ) * (x^3*y/2 - x^2*y^2/2 - x^2*z^2/2 - x*z^3 + y^3*z/2 + y^2*z^2)^2 + (3/4 : ℝ) * (-x^3*y - x^2*y^2 + x^2*z^2 + y^3*z)^2 := by positivity
  have hid : ( -(x * y + x * z + y * z) ^ 2 * (x * y ^ 3 + y * z ^ 3 + x ^ 3 * z) + (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 * z ^ 3 + x ^ 3 * y ^ 2 + y ^ 3 * z ^ 2) ) - ( 0  ) = (1 : ℝ) * (x^3*y/2 - x^2*y^2/2 - x^2*z^2/2 - x*z^3 + y^3*z/2 + y^2*z^2)^2 + (3/4 : ℝ) * (-x^3*y - x^2*y^2 + x^2*z^2 + y^3*z)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), -(x * y + x * z + y * z) ^ 2 * (x * y ^ 3 + y * z ^ 3 + x ^ 3 * z) + (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 * z ^ 3 + x ^ 3 * y ^ 2 + y ^ 3 * z ^ 2) ≥ 0) := @solution
#print axioms solution
