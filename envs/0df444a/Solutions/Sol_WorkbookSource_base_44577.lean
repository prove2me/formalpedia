-- Prove2me | solution 1 for WorkbookSource.base_44577
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:45:31.575679+00:00
-- url     : https://prove2.me/submissions/1272f70a-5ebe-470f-8171-241d17a6f4b4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a^2+b^2+c^2=1) : 6*a*b*c*(a+b+c)-2*(a*b+b*c+a*c)^2-(a*b+b*c+a*c)+1 ≥ 0  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a^2 + b^2 + c^2 - 1) := by linarith only [h]
  have hw4 : 0 ≤ (-a^2 - b^2 - c^2 + 1) := by linarith only [h]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (-a^2/2 + a*b - a*c/2 - b^2/2 - b*c/2 + c^2)^2 + (3/4 : ℝ) * (1) * (a^2 - a*c - b^2 + b*c)^2 + (1 : ℝ) * ((-a^2 - b^2 - c^2 + 1)) * (1)^2 + (1 : ℝ) * ((-a^2 - b^2 - c^2 + 1)) * (-a/2 - b/2 + c)^2 + (3/4 : ℝ) * ((-a^2 - b^2 - c^2 + 1)) * (-a + b)^2 := by positivity
  have hid : ( 6*a*b*c*(a+b+c)-2*(a*b+b*c+a*c)^2-(a*b+b*c+a*c)+1 ) - ( 0  ) = (1 : ℝ) * (1) * (-a^2/2 + a*b - a*c/2 - b^2/2 - b*c/2 + c^2)^2 + (3/4 : ℝ) * (1) * (a^2 - a*c - b^2 + b*c)^2 + (1 : ℝ) * ((-a^2 - b^2 - c^2 + 1)) * (1)^2 + (1 : ℝ) * ((-a^2 - b^2 - c^2 + 1)) * (-a/2 - b/2 + c)^2 + (3/4 : ℝ) * ((-a^2 - b^2 - c^2 + 1)) * (-a + b)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a^2+b^2+c^2=1), 6*a*b*c*(a+b+c)-2*(a*b+b*c+a*c)^2-(a*b+b*c+a*c)+1 ≥ 0) := @solution
#print axioms solution
