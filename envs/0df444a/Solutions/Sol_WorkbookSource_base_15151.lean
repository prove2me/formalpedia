-- Prove2me | solution 1 for WorkbookSource.base_15151
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:46.654344+00:00
-- url     : https://prove2.me/submissions/01ec5d3a-8450-4911-9a8d-ec9a3bcf0661

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a^2 + c^2 = 1) (hb : b^2 + 2 * b * (a + c) = 6) : b * (c - a) ≤ 4  := by
  have hw0 : 0 ≤ (a^2 + c^2 - 1) := by linarith only [ha]
  have hw1 : 0 ≤ (-a^2 - c^2 + 1) := by linarith only [ha]
  have hw2 : 0 ≤ (2*a*b + b^2 + 2*b*c - 6) := by linarith only [hb]
  have hw3 : 0 ≤ (-2*a*b - b^2 - 2*b*c + 6) := by linarith only [hb]
  have hsum : 0 ≤ (5/2 : ℝ) * (1) * (-b/10 + c)^2 + (5/2 : ℝ) * (1) * (a + 3*b/10)^2 + (1/4 : ℝ) * ((-2*a*b - b^2 - 2*b*c + 6)) * (1)^2 + (5/2 : ℝ) * ((-a^2 - c^2 + 1)) * (1)^2 := by positivity
  have hid : ( 4  ) - ( b * (c - a) ) = (5/2 : ℝ) * (1) * (-b/10 + c)^2 + (5/2 : ℝ) * (1) * (a + 3*b/10)^2 + (1/4 : ℝ) * ((-2*a*b - b^2 - 2*b*c + 6)) * (1)^2 + (5/2 : ℝ) * ((-a^2 - c^2 + 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a^2 + c^2 = 1) (hb : b^2 + 2 * b * (a + c) = 6), b * (c - a) ≤ 4) := @solution
#print axioms solution
