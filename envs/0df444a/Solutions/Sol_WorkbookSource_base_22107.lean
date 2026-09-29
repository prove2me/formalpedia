-- Prove2me | solution 1 for WorkbookSource.base_22107
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:28:20.322857+00:00
-- url     : https://prove2.me/submissions/f1f47a05-069e-41e3-ae38-2ad344e3b759

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (x y z : ℝ) :
  3 * (x ^ 4 + y ^ 4 + z ^ 4 - x ^ 3 * y - y ^ 3 * z - z ^ 3 * x) ^ 2 ≥
    2 * (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x) * (x ^ 3 + y ^ 3 + z ^ 3 - x ^ 2 * y - y ^ 2 * z - z ^ 2 * x) ^ 2  := by
  have hsum : 0 ≤ (13 : ℝ) * (7*x^4/26 + 5*x^3*z/13 - x^2*y^2/2 - 5*x^2*y*z/13 - x^2*z^2/2 + 2*x*y^3/13 - 2*x*y^2*z/13 + 7*x*y*z^2/13 - 5*y^4/26 + y^2*z^2 - 7*y*z^3/13 - z^4/13)^2 + (39/4 : ℝ) * (x^4/13 - 6*x^3*z/13 - x^2*y^2 + 6*x^2*y*z/13 + x^2*z^2 + 8*x*y^3/13 - 8*x*y^2*z/13 + 2*x*y*z^2/13 + 3*y^4/13 - 2*y*z^3/13 - 4*z^4/13)^2 := by positivity
  have hid : (
  3 * (x ^ 4 + y ^ 4 + z ^ 4 - x ^ 3 * y - y ^ 3 * z - z ^ 3 * x) ^ 2 ) - (
    2 * (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x) * (x ^ 3 + y ^ 3 + z ^ 3 - x ^ 2 * y - y ^ 2 * z - z ^ 2 * x) ^ 2  ) = (13 : ℝ) * (7*x^4/26 + 5*x^3*z/13 - x^2*y^2/2 - 5*x^2*y*z/13 - x^2*z^2/2 + 2*x*y^3/13 - 2*x*y^2*z/13 + 7*x*y*z^2/13 - 5*y^4/26 + y^2*z^2 - 7*y*z^3/13 - z^4/13)^2 + (39/4 : ℝ) * (x^4/13 - 6*x^3*z/13 - x^2*y^2 + 6*x^2*y*z/13 + x^2*z^2 + 8*x*y^3/13 - 8*x*y^2*z/13 + 2*x*y*z^2/13 + 3*y^4/13 - 2*y*z^3/13 - 4*z^4/13)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ), 3 * (x ^ 4 + y ^ 4 + z ^ 4 - x ^ 3 * y - y ^ 3 * z - z ^ 3 * x) ^ 2 ≥
    2 * (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - z * x) * (x ^ 3 + y ^ 3 + z ^ 3 - x ^ 2 * y - y ^ 2 * z - z ^ 2 * x) ^ 2) := @solution
#print axioms solution
