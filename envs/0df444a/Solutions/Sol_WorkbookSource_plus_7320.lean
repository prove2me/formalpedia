-- Prove2me | solution 1 for WorkbookSource.plus_7320
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:41:24.501025+00:00
-- url     : https://prove2.me/submissions/f5f66797-9bae-428a-9db6-02452afa4dee

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hab : x * y + y * z + z * x = 1) : (2 * (x + y + z) - 1) * (x + y + z - 2) + 5 * x * y * z ≥ 0   := by
  have hw0 : 0 ≤ (x) := by linarith only [hx]
  have hw1 : 0 ≤ (y) := by linarith only [hy]
  have hw2 : 0 ≤ (z) := by linarith only [hz]
  have hw3 : 0 ≤ (x*y + x*z + y*z - 1) := by linarith only [hab]
  have hw4 : 0 ≤ (-x*y - x*z - y*z + 1) := by linarith only [hab]
  have hsum : 0 ≤ (8 : ℝ) * (1) * (-x/2 - y/2 - z/2 + 1)^2 + (6 : ℝ) * ((x*y + x*z + y*z - 1)) * (1)^2 + (3/2 : ℝ) * ((z)) * (-x - y + 1)^2 + (3/2 : ℝ) * ((z) * (-x*y - x*z - y*z + 1)) * (1)^2 + (3/2 : ℝ) * ((y)) * (-x - z + 1)^2 + (3/2 : ℝ) * ((y) * (-x*y - x*z - y*z + 1)) * (1)^2 + (3/2 : ℝ) * ((x)) * (-y - z + 1)^2 + (3/2 : ℝ) * ((x) * (-x*y - x*z - y*z + 1)) * (1)^2 + (1/2 : ℝ) * ((x) * (y) * (z)) * (1)^2 := by positivity
  have hid : ( (2 * (x + y + z) - 1) * (x + y + z - 2) + 5 * x * y * z ) - ( 0   ) = (8 : ℝ) * (1) * (-x/2 - y/2 - z/2 + 1)^2 + (6 : ℝ) * ((x*y + x*z + y*z - 1)) * (1)^2 + (3/2 : ℝ) * ((z)) * (-x - y + 1)^2 + (3/2 : ℝ) * ((z) * (-x*y - x*z - y*z + 1)) * (1)^2 + (3/2 : ℝ) * ((y)) * (-x - z + 1)^2 + (3/2 : ℝ) * ((y) * (-x*y - x*z - y*z + 1)) * (1)^2 + (3/2 : ℝ) * ((x)) * (-y - z + 1)^2 + (3/2 : ℝ) * ((x) * (-x*y - x*z - y*z + 1)) * (1)^2 + (1/2 : ℝ) * ((x) * (y) * (z)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hab : x * y + y * z + z * x = 1), (2 * (x + y + z) - 1) * (x + y + z - 2) + 5 * x * y * z ≥ 0) := @solution
#print axioms solution
