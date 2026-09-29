-- Prove2me | solution 1 for WorkbookSource.base_41597
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:32:33.401984+00:00
-- url     : https://prove2.me/submissions/046fd6ce-1b81-4d84-8f46-5e25260ee48f

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (a b c x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (a^2 + b^2 + c^2) * (x^2 + y^2 + z^2 + x*y + x*z + y*z) ≥ 2 * (x + y + z) * (x*b*c + y*a*c + z*a*b)  := by
  have hsum : 0 ≤ (1 : ℝ) * (1) * (-a*x/2 - a*y/2 - b*x/2 - b*y/2 + c*x/2 + c*y/2 + c*z)^2 + (1 : ℝ) * (1) * (-a*x/2 - a*y/2 - a*z + b*x/2 + b*y/2 + b*z - c*x/2 + c*y/2)^2 + (1/2 : ℝ) * (1) * (-a*y - b*x + c*x + c*y)^2 + (1/2 : ℝ) * (1) * (-a*x + b*y)^2 := by positivity
  have hid : ( (a^2 + b^2 + c^2) * (x^2 + y^2 + z^2 + x*y + x*z + y*z) ) - ( 2 * (x + y + z) * (x*b*c + y*a*c + z*a*b)  ) = (1 : ℝ) * (1) * (-a*x/2 - a*y/2 - b*x/2 - b*y/2 + c*x/2 + c*y/2 + c*z)^2 + (1 : ℝ) * (1) * (-a*x/2 - a*y/2 - a*z + b*x/2 + b*y/2 + b*z - c*x/2 + c*y/2)^2 + (1/2 : ℝ) * (1) * (-a*y - b*x + c*x + c*y)^2 + (1/2 : ℝ) * (1) * (-a*x + b*y)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), (a^2 + b^2 + c^2) * (x^2 + y^2 + z^2 + x*y + x*z + y*z) ≥ 2 * (x + y + z) * (x*b*c + y*a*c + z*a*b)) := @solution
#print axioms solution
