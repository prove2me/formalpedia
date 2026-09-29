-- Prove2me | solution 1 for WorkbookSource.plus_68327
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:20:11.564793+00:00
-- url     : https://prove2.me/submissions/cf3757a5-caa0-41b5-a8f4-d571327abc76

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y z a b c : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : x^2 + y^2 + z^2 + a^2 + b^2 + c^2 - a * (y + z) - b * (z + x) - c * (x + y) ≥ (1 / 3) * (a + b + c - x - y - z)^2   := by
  have hw0 : 0 ≤ (x) := by linarith only [hx]
  have hw1 : 0 ≤ (y) := by linarith only [hy]
  have hw2 : 0 ≤ (z) := by linarith only [hz]
  have hw3 : 0 ≤ (a) := by linarith only [ha]
  have hw4 : 0 ≤ (b) := by linarith only [hb]
  have hw5 : 0 ≤ (c) := by linarith only [hc]
  have hsum : 0 ≤ (2/3 : ℝ) * (1) * (-a/2 - b/2 + c - x/4 - y/4 + z/2)^2 + (5/8 : ℝ) * (1) * (-2*a/5 + 2*b/5 - 3*x/5 + y - 2*z/5)^2 + (2/5 : ℝ) * (1) * (-a + b - x/4 + z/4)^2 + (3/8 : ℝ) * (1) * (-x + z)^2 := by positivity
  have hid : ( x^2 + y^2 + z^2 + a^2 + b^2 + c^2 - a * (y + z) - b * (z + x) - c * (x + y) ) - ( (1 / 3) * (a + b + c - x - y - z)^2   ) = (2/3 : ℝ) * (1) * (-a/2 - b/2 + c - x/4 - y/4 + z/2)^2 + (5/8 : ℝ) * (1) * (-2*a/5 + 2*b/5 - 3*x/5 + y - 2*z/5)^2 + (2/5 : ℝ) * (1) * (-a + b - x/4 + z/4)^2 + (3/8 : ℝ) * (1) * (-x + z)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y z a b c : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), x^2 + y^2 + z^2 + a^2 + b^2 + c^2 - a * (y + z) - b * (z + x) - c * (x + y) ≥ (1 / 3) * (a + b + c - x - y - z)^2) := @solution
#print axioms solution
