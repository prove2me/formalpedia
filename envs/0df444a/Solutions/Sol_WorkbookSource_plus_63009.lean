-- Prove2me | solution 1 for WorkbookSource.plus_63009
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:42.487484+00:00
-- url     : https://prove2.me/submissions/3123c392-e2c0-4c90-a75f-6fd945f62190

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : 2*a + b + 3*c = 20) : a^2 + 4*b^2 + c^2 ≥ 1600/53   := by
  have hw0 : 0 ≤ (2*a + b + 3*c - 20) := by linarith only [h]
  have hw1 : 0 ≤ (-2*a - b - 3*c + 20) := by linarith only [h]
  have hsum : 0 ≤ (1600/53 : ℝ) * (1) * (-a/10 - b/20 - 3*c/20 + 1)^2 + (208/53 : ℝ) * (1) * (-a/26 + b - 3*c/52)^2 + (9/13 : ℝ) * (1) * (a - 2*c/3)^2 + (160/53 : ℝ) * ((2*a + b + 3*c - 20)) * (1)^2 := by positivity
  have hid : ( a^2 + 4*b^2 + c^2 ) - ( 1600/53   ) = (1600/53 : ℝ) * (1) * (-a/10 - b/20 - 3*c/20 + 1)^2 + (208/53 : ℝ) * (1) * (-a/26 + b - 3*c/52)^2 + (9/13 : ℝ) * (1) * (a - 2*c/3)^2 + (160/53 : ℝ) * ((2*a + b + 3*c - 20)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : 2*a + b + 3*c = 20), a^2 + 4*b^2 + c^2 ≥ 1600/53) := @solution
#print axioms solution
