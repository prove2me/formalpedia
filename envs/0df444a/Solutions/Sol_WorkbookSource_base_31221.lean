-- Prove2me | solution 1 for WorkbookSource.base_31221
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:45:21.313599+00:00
-- url     : https://prove2.me/submissions/ce0c1802-550e-48b8-8e8c-99aa2749d390

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a^2 + b^2 + c^2 = 3) :
  a + b + c - (a - b) * (a - c) ≤ 3  := by
  have hw0 : 0 ≤ (a^2 + b^2 + c^2 - 3) := by linarith only [h]
  have hw1 : 0 ≤ (-a^2 - b^2 - c^2 + 3) := by linarith only [h]
  have hsum : 0 ≤ (3/2 : ℝ) * (1) * (-a/3 - b/3 - c/3 + 1)^2 + (4/3 : ℝ) * (1) * (a - b/2 - c/2)^2 + (1/2 : ℝ) * ((-a^2 - b^2 - c^2 + 3)) * (1)^2 := by positivity
  have hid : ( 3  ) - (
  a + b + c - (a - b) * (a - c) ) = (3/2 : ℝ) * (1) * (-a/3 - b/3 - c/3 + 1)^2 + (4/3 : ℝ) * (1) * (a - b/2 - c/2)^2 + (1/2 : ℝ) * ((-a^2 - b^2 - c^2 + 3)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a^2 + b^2 + c^2 = 3), a + b + c - (a - b) * (a - c) ≤ 3) := @solution
#print axioms solution
