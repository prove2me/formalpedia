-- Prove2me | solution 1 for WorkbookSource.base_45142
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:29.893659+00:00
-- url     : https://prove2.me/submissions/b12aa487-900a-428e-9d69-238a8809c1f1

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y : ℝ) (h : x + y ≥ 0) : x^7 + y^7 - x^6*y - x*y^6 + x^2 + 4*x ≥ -4  := by
  have hw0 : 0 ≤ (x + y) := by linarith only [h]
  have hsum : 0 ≤ (4 : ℝ) * (1) * (x/2 + 1)^2 + (1 : ℝ) * ((x + y)) * (-x^3/2 + x^2*y/2 - x*y^2 + y^3)^2 + (3/4 : ℝ) * ((x + y)) * (-x^3 + x^2*y)^2 := by positivity
  have hid : ( x^7 + y^7 - x^6*y - x*y^6 + x^2 + 4*x ) - ( -4  ) = (4 : ℝ) * (1) * (x/2 + 1)^2 + (1 : ℝ) * ((x + y)) * (-x^3/2 + x^2*y/2 - x*y^2 + y^3)^2 + (3/4 : ℝ) * ((x + y)) * (-x^3 + x^2*y)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y : ℝ) (h : x + y ≥ 0), x^7 + y^7 - x^6*y - x*y^6 + x^2 + 4*x ≥ -4) := @solution
#print axioms solution
