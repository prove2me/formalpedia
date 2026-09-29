-- Prove2me | solution 1 for WorkbookCorrected.base_6994
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:29:28.39168+00:00
-- url     : https://prove2.me/submissions/fe634858-a211-4474-b84a-5d7cfa226105

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : -x*y*z*(x^2*y^3 + y^2*z^3 + x^3*z^2) + (1/3)*(x^2*y^2 + y^2*z^2 + x^2*z^2)^2 ≥ 0  := by
  have hsum : 0 ≤ (1 : ℝ) * (x^2*y^2/2 - x^2*y*z/2 - x*y^2*z/2 + x*y*z^2 - y^2*z^2/2)^2 + (3/4 : ℝ) * (-x^2*y^2/3 - x^2*y*z + 2*x^2*z^2/3 + x*y^2*z - y^2*z^2/3)^2 := by positivity
  have hid : ( -x*y*z*(x^2*y^3 + y^2*z^3 + x^3*z^2) + (1/3)*(x^2*y^2 + y^2*z^2 + x^2*z^2)^2 ) - ( 0  ) = (1 : ℝ) * (x^2*y^2/2 - x^2*y*z/2 - x*y^2*z/2 + x*y*z^2 - y^2*z^2/2)^2 + (3/4 : ℝ) * (-x^2*y^2/3 - x^2*y*z + 2*x^2*z^2/3 + x*y^2*z - y^2*z^2/3)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), -x*y*z*(x^2*y^3 + y^2*z^3 + x^3*z^2) + (1/3)*(x^2*y^2 + y^2*z^2 + x^2*z^2)^2 ≥ 0) := @solution
#print axioms solution
