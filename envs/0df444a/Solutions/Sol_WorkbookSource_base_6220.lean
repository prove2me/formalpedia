-- Prove2me | solution 1 for WorkbookSource.base_6220
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:18:46.534826+00:00
-- url     : https://prove2.me/submissions/88309310-fe6a-40b1-9d6d-d3a24a16e0ce

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (h : x + y + z ≥ 3) :
  x^2*y^2*z^2 + 1/27 * (x + y + z)^3 ≥ 2/3 * (x + y + z) * x * y * z  := by
  have hw0 : 0 ≤ (x + y + z - 3) := by linarith only [h]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (x*y*z - x/3 - y/3 - z/3)^2 + (1/27 : ℝ) * ((x + y + z - 3)) * (x + y + z)^2 := by positivity
  have hid : (
  x^2*y^2*z^2 + 1/27 * (x + y + z)^3 ) - ( 2/3 * (x + y + z) * x * y * z  ) = (1 : ℝ) * (1) * (x*y*z - x/3 - y/3 - z/3)^2 + (1/27 : ℝ) * ((x + y + z - 3)) * (x + y + z)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (h : x + y + z ≥ 3), x^2*y^2*z^2 + 1/27 * (x + y + z)^3 ≥ 2/3 * (x + y + z) * x * y * z) := @solution
#print axioms solution
