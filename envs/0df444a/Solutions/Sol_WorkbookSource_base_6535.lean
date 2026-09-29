-- Prove2me | solution 1 for WorkbookSource.base_6535
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:25:07.274831+00:00
-- url     : https://prove2.me/submissions/c759810e-1896-44e6-a2e8-de4744289fa4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution  (x y z : ℝ) :
  (x^2 + y^2 + z^2) * (x^6 + y^6 + z^6) ≥ (x^5 + y^5 + z^5) * (x^3 + y^3 + z^3)  := by
  have hsum : 0 ≤ (1 : ℝ) * (-y^3*z/2 - y^2*z^2/2 + y*z^3)^2 + (1 : ℝ) * (-x^3*z/2 - x^2*z^2/2 + x*z^3)^2 + (1 : ℝ) * (-x^3*y/2 - x^2*y^2/2 + x*y^3)^2 + (3/4 : ℝ) * (-y^3*z + y^2*z^2)^2 + (3/4 : ℝ) * (-x^3*z + x^2*z^2)^2 + (3/4 : ℝ) * (-x^3*y + x^2*y^2)^2 := by positivity
  have hid : (
  (x^2 + y^2 + z^2) * (x^6 + y^6 + z^6) ) - ( (x^5 + y^5 + z^5) * (x^3 + y^3 + z^3)  ) = (1 : ℝ) * (-y^3*z/2 - y^2*z^2/2 + y*z^3)^2 + (1 : ℝ) * (-x^3*z/2 - x^2*z^2/2 + x*z^3)^2 + (1 : ℝ) * (-x^3*y/2 - x^2*y^2/2 + x*y^3)^2 + (3/4 : ℝ) * (-y^3*z + y^2*z^2)^2 + (3/4 : ℝ) * (-x^3*z + x^2*z^2)^2 + (3/4 : ℝ) * (-x^3*y + x^2*y^2)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ), (x^2 + y^2 + z^2) * (x^6 + y^6 + z^6) ≥ (x^5 + y^5 + z^5) * (x^3 + y^3 + z^3)) := @solution
#print axioms solution
