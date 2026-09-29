-- Prove2me | solution 1 for WorkbookSource.plus_7401
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:35.036795+00:00
-- url     : https://prove2.me/submissions/3845c51f-c8d0-4169-b3e7-a3198e09212b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b^2 + c^2 = 4) : a + b^2 + c^3 ≥ 104 / 27   := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a + b^2 + c^2 - 4) := by linarith only [habc]
  have hw4 : 0 ≤ (-a - b^2 - c^2 + 4) := by linarith only [habc]
  have hsum : 0 ≤ (1/3 : ℝ) * (1) * (c - 2/3)^2 + (1 : ℝ) * ((a + b^2 + c^2 - 4)) * (1)^2 + (1 : ℝ) * ((c)) * (c - 2/3)^2 := by positivity
  have hid : ( a + b^2 + c^3 ) - ( 104 / 27   ) = (1/3 : ℝ) * (1) * (c - 2/3)^2 + (1 : ℝ) * ((a + b^2 + c^2 - 4)) * (1)^2 + (1 : ℝ) * ((c)) * (c - 2/3)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b^2 + c^2 = 4), a + b^2 + c^3 ≥ 104 / 27) := @solution
#print axioms solution
