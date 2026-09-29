-- Prove2me | solution 1 for WorkbookSource.plus_18705
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:46:26.185853+00:00
-- url     : https://prove2.me/submissions/c9790e62-60a1-413a-a38c-083d1bef5fe4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (habc : x*y*z = 1) : x^2 * (2*y - 1)^2 + y^2 * (2*z - 1)^2 + z^2 * (2*x - 1)^2 + 5 ≥ (1 + x) * (1 + y) * (1 + z) + 3 * (1 - x) * (1 - y) * (1 - z)   := by
  have hw0 : 0 ≤ (x) := by linarith only [hx]
  have hw1 : 0 ≤ (y) := by linarith only [hy]
  have hw2 : 0 ≤ (z) := by linarith only [hz]
  have hw3 : 0 ≤ (x*y*z - 1) := by linarith only [habc]
  have hw4 : 0 ≤ (-x*y*z + 1) := by linarith only [habc]
  have hsum : 0 ≤ (4 : ℝ) * (1) * (y*z - y/2 - 1/2)^2 + (4 : ℝ) * (1) * (x*z - z/2 - 1/2)^2 + (4 : ℝ) * (1) * (x*y - x/2 - 1/2)^2 + (2 : ℝ) * ((x*y*z - 1)) * (1)^2 := by positivity
  have hid : ( x^2 * (2*y - 1)^2 + y^2 * (2*z - 1)^2 + z^2 * (2*x - 1)^2 + 5 ) - ( (1 + x) * (1 + y) * (1 + z) + 3 * (1 - x) * (1 - y) * (1 - z)   ) = (4 : ℝ) * (1) * (y*z - y/2 - 1/2)^2 + (4 : ℝ) * (1) * (x*z - z/2 - 1/2)^2 + (4 : ℝ) * (1) * (x*y - x/2 - 1/2)^2 + (2 : ℝ) * ((x*y*z - 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (habc : x*y*z = 1), x^2 * (2*y - 1)^2 + y^2 * (2*z - 1)^2 + z^2 * (2*x - 1)^2 + 5 ≥ (1 + x) * (1 + y) * (1 + z) + 3 * (1 - x) * (1 - y) * (1 - z)) := @solution
#print axioms solution
