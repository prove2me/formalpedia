-- Prove2me | solution 1 for WorkbookSource.plus_6754
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:46:24.313266+00:00
-- url     : https://prove2.me/submissions/60c43495-d083-4bf8-a999-98897f1b94a4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (h : 2*x^2 + 3*y^2 + 4*z^2 = 1) :
  (4*x - 3*y - 2*z)^2 ≤ 12   := by
  have hw0 : 0 ≤ (2*x^2 + 3*y^2 + 4*z^2 - 1) := by linarith only [h]
  have hw1 : 0 ≤ (-2*x^2 - 3*y^2 - 4*z^2 + 1) := by linarith only [h]
  have hsum : 0 ≤ (44 : ℝ) * (1) * (2*x/11 - 3*y/22 + z)^2 + (288/11 : ℝ) * (1) * (x/2 + y)^2 + (12 : ℝ) * ((-2*x^2 - 3*y^2 - 4*z^2 + 1)) * (1)^2 := by positivity
  have hid : ( 12   ) - (
  (4*x - 3*y - 2*z)^2 ) = (44 : ℝ) * (1) * (2*x/11 - 3*y/22 + z)^2 + (288/11 : ℝ) * (1) * (x/2 + y)^2 + (12 : ℝ) * ((-2*x^2 - 3*y^2 - 4*z^2 + 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (h : 2*x^2 + 3*y^2 + 4*z^2 = 1), (4*x - 3*y - 2*z)^2 ≤ 12) := @solution
#print axioms solution
