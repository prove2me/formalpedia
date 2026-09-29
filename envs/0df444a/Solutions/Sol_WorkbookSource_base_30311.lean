-- Prove2me | solution 1 for WorkbookSource.base_30311
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:31.989702+00:00
-- url     : https://prove2.me/submissions/69fc7acf-cbba-4c57-a1cd-63e8c6143b27

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^2 + b^2 = 2) : a + b + (1 / 16) * (a^2 - b^2)^2 ≤ 2  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (a^2 + b^2 - 2) := by linarith only [hab]
  have hw3 : 0 ≤ (-a^2 - b^2 + 2) := by linarith only [hab]
  have hsum : 0 ≤ (5/9 : ℝ) * (1) * (a^2/4 - 3*a*b/10 - 3*a/5 + b^2/4 - 3*b/5 + 1)^2 + (1/5 : ℝ) * (1) * (a*b - a/2 - b/2)^2 + (13/18 : ℝ) * ((-a^2 - b^2 + 2)) * (-3*a/26 - 3*b/26 + 1)^2 + (41/468 : ℝ) * ((-a^2 - b^2 + 2)) * (-24*a/41 + b)^2 + (85/1476 : ℝ) * ((-a^2 - b^2 + 2)) * (a)^2 := by positivity
  have hid : ( 2  ) - ( a + b + (1 / 16) * (a^2 - b^2)^2 ) = (5/9 : ℝ) * (1) * (a^2/4 - 3*a*b/10 - 3*a/5 + b^2/4 - 3*b/5 + 1)^2 + (1/5 : ℝ) * (1) * (a*b - a/2 - b/2)^2 + (13/18 : ℝ) * ((-a^2 - b^2 + 2)) * (-3*a/26 - 3*b/26 + 1)^2 + (41/468 : ℝ) * ((-a^2 - b^2 + 2)) * (-24*a/41 + b)^2 + (85/1476 : ℝ) * ((-a^2 - b^2 + 2)) * (a)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a^2 + b^2 = 2), a + b + (1 / 16) * (a^2 - b^2)^2 ≤ 2) := @solution
#print axioms solution
