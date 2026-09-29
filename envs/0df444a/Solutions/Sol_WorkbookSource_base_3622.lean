-- Prove2me | solution 1 for WorkbookSource.base_3622
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:41.155015+00:00
-- url     : https://prove2.me/submissions/1922ecad-fa69-4ea5-a44c-82ea92a23cbb

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a = 3) : (a + b) * (a + b * c) + (b + c) * (b + c * a) + (c + a) * (c + a * b) ≥ 12  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a*b + a*c + b*c - 3) := by linarith only [hab]
  have hw4 : 0 ≤ (-a*b - a*c - b*c + 3) := by linarith only [hab]
  have hsum : 0 ≤ (6 : ℝ) * (1) * (-a/3 - b/3 - c/3 + 1)^2 + (1/3 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (1/4 : ℝ) * (1) * (-a + b)^2 + (6 : ℝ) * ((a*b + a*c + b*c - 3)) * (1)^2 + (3 : ℝ) * ((c)) * (-a/3 - 2*b/3 + 1)^2 + (1/3 : ℝ) * ((c) * (-a*b - a*c - b*c + 3)) * (1)^2 + (3 : ℝ) * ((b)) * (-2*a/3 - c/3 + 1)^2 + (1/3 : ℝ) * ((b) * (-a*b - a*c - b*c + 3)) * (1)^2 + (3 : ℝ) * ((a)) * (-b/3 - 2*c/3 + 1)^2 + (1/3 : ℝ) * ((a) * (-a*b - a*c - b*c + 3)) * (1)^2 := by positivity
  have hid : ( (a + b) * (a + b * c) + (b + c) * (b + c * a) + (c + a) * (c + a * b) ) - ( 12  ) = (6 : ℝ) * (1) * (-a/3 - b/3 - c/3 + 1)^2 + (1/3 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (1/4 : ℝ) * (1) * (-a + b)^2 + (6 : ℝ) * ((a*b + a*c + b*c - 3)) * (1)^2 + (3 : ℝ) * ((c)) * (-a/3 - 2*b/3 + 1)^2 + (1/3 : ℝ) * ((c) * (-a*b - a*c - b*c + 3)) * (1)^2 + (3 : ℝ) * ((b)) * (-2*a/3 - c/3 + 1)^2 + (1/3 : ℝ) * ((b) * (-a*b - a*c - b*c + 3)) * (1)^2 + (3 : ℝ) * ((a)) * (-b/3 - 2*c/3 + 1)^2 + (1/3 : ℝ) * ((a) * (-a*b - a*c - b*c + 3)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a = 3), (a + b) * (a + b * c) + (b + c) * (b + c * a) + (c + a) * (c + a * b) ≥ 12) := @solution
#print axioms solution
