-- Prove2me | solution 1 for WorkbookSource.base_7402
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:20.643674+00:00
-- url     : https://prove2.me/submissions/c568891e-9a23-47cc-949d-bd4b0da313a8

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : a^2 + b^2 = 1) (hb : c * d = 2) : (a - d)^2 + (b - c)^2 ≥ 1  := by
  have hw0 : 0 ≤ (a^2 + b^2 - 1) := by linarith only [ha]
  have hw1 : 0 ≤ (-a^2 - b^2 + 1) := by linarith only [ha]
  have hw2 : 0 ≤ (c*d - 2) := by linarith only [hb]
  have hw3 : 0 ≤ (-c*d + 2) := by linarith only [hb]
  have hsum : 0 ≤ (2 : ℝ) * (1) * (b - c/2)^2 + (2 : ℝ) * (1) * (a - d/2)^2 + (1/2 : ℝ) * (1) * (-c + d)^2 + (1 : ℝ) * ((c*d - 2)) * (1)^2 + (1 : ℝ) * ((-a^2 - b^2 + 1)) * (1)^2 := by positivity
  have hid : ( (a - d)^2 + (b - c)^2 ) - ( 1  ) = (2 : ℝ) * (1) * (b - c/2)^2 + (2 : ℝ) * (1) * (a - d/2)^2 + (1/2 : ℝ) * (1) * (-c + d)^2 + (1 : ℝ) * ((c*d - 2)) * (1)^2 + (1 : ℝ) * ((-a^2 - b^2 + 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (ha : a^2 + b^2 = 1) (hb : c * d = 2), (a - d)^2 + (b - c)^2 ≥ 1) := @solution
#print axioms solution
