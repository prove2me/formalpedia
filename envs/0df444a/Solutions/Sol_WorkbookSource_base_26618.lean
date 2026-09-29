-- Prove2me | solution 1 for WorkbookSource.base_26618
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:27:53.800268+00:00
-- url     : https://prove2.me/submissions/cb848c8c-4b98-440c-9204-6aeb21fbf891

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (x y z : ℝ) : (x^4 + y^4 + z^4) * (x^2 * y^4 + y^2 * z^4 + z^2 * x^4) ≥ (x * y^4 + y * z^4 + z * x^4)^2  := by
  have hsum : 0 ≤ (1 : ℝ) * (-x*y^2*z^2 + y^3*z^2)^2 + (1 : ℝ) * (-x^2*y*z^2 + x^2*z^3)^2 + (1 : ℝ) * (-x^3*y^2 + x^2*y^2*z)^2 := by positivity
  have hid : ( (x^4 + y^4 + z^4) * (x^2 * y^4 + y^2 * z^4 + z^2 * x^4) ) - ( (x * y^4 + y * z^4 + z * x^4)^2  ) = (1 : ℝ) * (-x*y^2*z^2 + y^3*z^2)^2 + (1 : ℝ) * (-x^2*y*z^2 + x^2*z^3)^2 + (1 : ℝ) * (-x^3*y^2 + x^2*y^2*z)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ), (x^4 + y^4 + z^4) * (x^2 * y^4 + y^2 * z^4 + z^2 * x^4) ≥ (x * y^4 + y * z^4 + z * x^4)^2) := @solution
#print axioms solution
