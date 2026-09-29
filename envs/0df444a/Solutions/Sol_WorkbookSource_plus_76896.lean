-- Prove2me | solution 1 for WorkbookSource.plus_76896
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:46:32.203188+00:00
-- url     : https://prove2.me/submissions/1f05c9fc-c6fd-4e86-a52e-53005ee85c3c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a^2 + b^2 + c^2 = 1) (hb : 2 * a + 2 * b - 3 * c = 1) : 20 * a^2 + 25 * b^2 + 13 * c^2 - 12 * a * b + 16 * b * c + 24 * c * a ≥ 25   := by
  have hw0 : 0 ≤ (a^2 + b^2 + c^2 - 1) := by linarith only [ha]
  have hw1 : 0 ≤ (-a^2 - b^2 - c^2 + 1) := by linarith only [ha]
  have hw2 : 0 ≤ (2*a + 2*b - 3*c - 1) := by linarith only [hb]
  have hw3 : 0 ≤ (-2*a - 2*b + 3*c + 1) := by linarith only [hb]
  have hsum : 0 ≤ (8 : ℝ) * (1) * (-3*a/8 - 7*b/8 + c)^2 + (11/8 : ℝ) * (1) * (a + b)^2 + (5 : ℝ) * ((-2*a - 2*b + 3*c + 1)) * (1)^2 + (5/2 : ℝ) * ((2*a + 2*b - 3*c - 1) * (-2*a - 2*b + 3*c + 1)) * (1)^2 + (55/2 : ℝ) * ((a^2 + b^2 + c^2 - 1)) * (1)^2 := by positivity
  have hid : ( 20 * a^2 + 25 * b^2 + 13 * c^2 - 12 * a * b + 16 * b * c + 24 * c * a ) - ( 25   ) = (8 : ℝ) * (1) * (-3*a/8 - 7*b/8 + c)^2 + (11/8 : ℝ) * (1) * (a + b)^2 + (5 : ℝ) * ((-2*a - 2*b + 3*c + 1)) * (1)^2 + (5/2 : ℝ) * ((2*a + 2*b - 3*c - 1) * (-2*a - 2*b + 3*c + 1)) * (1)^2 + (55/2 : ℝ) * ((a^2 + b^2 + c^2 - 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a^2 + b^2 + c^2 = 1) (hb : 2 * a + 2 * b - 3 * c = 1), 20 * a^2 + 25 * b^2 + 13 * c^2 - 12 * a * b + 16 * b * c + 24 * c * a ≥ 25) := @solution
#print axioms solution
