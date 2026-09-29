-- Prove2me | solution 1 for WorkbookSource.base_8693
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:27:29.004988+00:00
-- url     : https://prove2.me/submissions/72ead8d9-76a2-49fc-aa4f-b94031ffdc51

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (x y z : ℝ) : (y^2 + z^2)^2 * (z^2 + x^2)^2 ≥ 4 * z^4 * (y + x)^2 * x * y  := by
  have hsum : 0 ≤ (2 : ℝ) * (-x*y^2*z + y*z^3)^2 + (2 : ℝ) * (-x^2*y*z + x*z^3)^2 + (1 : ℝ) * (-x^2*y^2 + z^4)^2 + (1 : ℝ) * (-x^2*z^2 + y^2*z^2)^2 := by positivity
  have hid : ( (y^2 + z^2)^2 * (z^2 + x^2)^2 ) - ( 4 * z^4 * (y + x)^2 * x * y  ) = (2 : ℝ) * (-x*y^2*z + y*z^3)^2 + (2 : ℝ) * (-x^2*y*z + x*z^3)^2 + (1 : ℝ) * (-x^2*y^2 + z^4)^2 + (1 : ℝ) * (-x^2*z^2 + y^2*z^2)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ), (y^2 + z^2)^2 * (z^2 + x^2)^2 ≥ 4 * z^4 * (y + x)^2 * x * y) := @solution
#print axioms solution
