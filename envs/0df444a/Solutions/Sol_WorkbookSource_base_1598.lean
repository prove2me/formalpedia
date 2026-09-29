-- Prove2me | solution 1 for WorkbookSource.base_1598
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:11:09.545541+00:00
-- url     : https://prove2.me/submissions/81ee1413-0fea-4106-8561-dee4bf3abe50

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (h : x + y + z = 1) : 2*x^2 + 3*y^2 + 4*z^2 ≥ 12/13  := by
  have hw0 : 0 ≤ (x + y + z - 1) := by linarith only [h]
  have hw1 : 0 ≤ (-x - y - z + 1) := by linarith only [h]
  have hsum : 0 ≤ (4 : ℝ) * (1) * (z - 3/13)^2 + (3 : ℝ) * (1) * (y - 4/13)^2 + (2 : ℝ) * (1) * (x - 6/13)^2 + (24/13 : ℝ) * ((x + y + z - 1)) * (1)^2 := by positivity
  have hid : ( 2*x^2 + 3*y^2 + 4*z^2 ) - ( 12/13  ) = (4 : ℝ) * (1) * (z - 3/13)^2 + (3 : ℝ) * (1) * (y - 4/13)^2 + (2 : ℝ) * (1) * (x - 6/13)^2 + (24/13 : ℝ) * ((x + y + z - 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (h : x + y + z = 1), 2*x^2 + 3*y^2 + 4*z^2 ≥ 12/13) := @solution
#print axioms solution
