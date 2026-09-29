-- Prove2me | solution 1 for WorkbookSource.base_21512
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:17:01.935426+00:00
-- url     : https://prove2.me/submissions/cae117cf-7265-42cd-9922-214c1523cb15

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (x y z : ℝ) :
  (x^2 + y^2 + z^2 - x * y - x * z - y * z)^3 ≥ (27 / 4) * (x - y)^2 * (y - z)^2 * (z - x)^2  := by
  have h0 : 0 ≤ (36 : ℝ) * (x^3/6 - x^2*y/4 - x^2*z/4 - x*y^2/4 + x*y*z - x*z^2/4 + y^3/6 - y^2*z/4 - y*z^2/4 + z^3/6)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0]
example : (∀ (x y z : ℝ), (x^2 + y^2 + z^2 - x * y - x * z - y * z)^3 ≥ (27 / 4) * (x - y)^2 * (y - z)^2 * (z - x)^2) := @solution
#print axioms solution
