-- Prove2me | solution 1 for WorkbookSource.base_41374
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:28:32.765899+00:00
-- url     : https://prove2.me/submissions/1426acfc-4f91-423e-93bf-01b4ece42ba4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (h : x + 3 * y + z = 0) :
  (x^2 + y^2 + z^2)^3 ≥ (38/27) * (x^3 + y^3 + z^3)^2  := by
  have helim : z = (-x - 3*y) := by linarith only [h]
  have hsum : 0 ≤ (514/3 : ℝ) * (54*x^3/257 + x^2*y + 213*x*y^2/257 - 380*y^3/771)^2 + (107632/2313 : ℝ) * (-3*x^3/31 + x*y^2 - 12*y^3/31)^2 := by positivity
  have hid : (
  (x^2 + y^2 + z^2)^3 ) - ( (38/27) * (x^3 + y^3 + z^3)^2  ) = (514/3 : ℝ) * (54*x^3/257 + x^2*y + 213*x*y^2/257 - 380*y^3/771)^2 + (107632/2313 : ℝ) * (-3*x^3/31 + x*y^2 - 12*y^3/31)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (h : x + 3 * y + z = 0), (x^2 + y^2 + z^2)^3 ≥ (38/27) * (x^3 + y^3 + z^3)^2) := @solution
#print axioms solution
