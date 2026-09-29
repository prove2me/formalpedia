-- Prove2me | solution 1 for WorkbookSource.plus_4724
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:20:07.398411+00:00
-- url     : https://prove2.me/submissions/a2005f02-444e-4f59-a7b3-8da952acf088

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x + y + z) ^ 2 ≤ (4 / 3) * (1 + x ^ 2) * (1 + y ^ 2) * (1 + z ^ 2)   := by
  have hw0 : 0 ≤ (x) := by linarith only [hx]
  have hw1 : 0 ≤ (y) := by linarith only [hy]
  have hw2 : 0 ≤ (z) := by linarith only [hz]
  have hsum : 0 ≤ (4/3 : ℝ) * (1) * (-2*x*y/3 - 2*x*z/3 - 2*y*z/3 + 1)^2 + (4/3 : ℝ) * (1) * (x*y*z - x/6 - y/6 - z/6)^2 + (20/27 : ℝ) * (1) * (-x*y/2 - x*z/2 + y*z)^2 + (5/9 : ℝ) * (1) * (-x*y + x*z)^2 + (8/27 : ℝ) * (1) * (-x/2 - y/2 + z)^2 + (2/9 : ℝ) * (1) * (-x + y)^2 := by positivity
  have hid : ( (4 / 3) * (1 + x ^ 2) * (1 + y ^ 2) * (1 + z ^ 2)   ) - ( (x + y + z) ^ 2 ) = (4/3 : ℝ) * (1) * (-2*x*y/3 - 2*x*z/3 - 2*y*z/3 + 1)^2 + (4/3 : ℝ) * (1) * (x*y*z - x/6 - y/6 - z/6)^2 + (20/27 : ℝ) * (1) * (-x*y/2 - x*z/2 + y*z)^2 + (5/9 : ℝ) * (1) * (-x*y + x*z)^2 + (8/27 : ℝ) * (1) * (-x/2 - y/2 + z)^2 + (2/9 : ℝ) * (1) * (-x + y)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z), (x + y + z) ^ 2 ≤ (4 / 3) * (1 + x ^ 2) * (1 + y ^ 2) * (1 + z ^ 2)) := @solution
#print axioms solution
