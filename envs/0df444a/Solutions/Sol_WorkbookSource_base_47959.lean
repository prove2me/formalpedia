-- Prove2me | solution 1 for WorkbookSource.base_47959
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:46:20.530688+00:00
-- url     : https://prove2.me/submissions/ccfce60f-85e0-4f85-9f73-0e38ce2ef2d5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b + a * c + b * c = 3) : 8 * (a + b + c) ^ 2 ≥ 9 * (a + b) * (a + c) * (b + c)  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a*b + a*c + b*c - 3) := by linarith only [habc]
  have hw4 : 0 ≤ (-a*b - a*c - b*c + 3) := by linarith only [habc]
  have hsum : 0 ≤ (72 : ℝ) * (1) * (-a/3 - b/3 - c/3 + 1)^2 + (24 : ℝ) * ((a*b + a*c + b*c - 3)) * (1)^2 + (12 : ℝ) * ((c)) * (-a/2 - b/2 + 1)^2 + (12 : ℝ) * ((c) * (-a*b - a*c - b*c + 3)) * (1)^2 + (12 : ℝ) * ((b)) * (-a/2 - c/2 + 1)^2 + (12 : ℝ) * ((b) * (-a*b - a*c - b*c + 3)) * (1)^2 + (12 : ℝ) * ((a)) * (-b/2 - c/2 + 1)^2 + (12 : ℝ) * ((a) * (-a*b - a*c - b*c + 3)) * (1)^2 := by positivity
  have hid : ( 8 * (a + b + c) ^ 2 ) - ( 9 * (a + b) * (a + c) * (b + c)  ) = (72 : ℝ) * (1) * (-a/3 - b/3 - c/3 + 1)^2 + (24 : ℝ) * ((a*b + a*c + b*c - 3)) * (1)^2 + (12 : ℝ) * ((c)) * (-a/2 - b/2 + 1)^2 + (12 : ℝ) * ((c) * (-a*b - a*c - b*c + 3)) * (1)^2 + (12 : ℝ) * ((b)) * (-a/2 - c/2 + 1)^2 + (12 : ℝ) * ((b) * (-a*b - a*c - b*c + 3)) * (1)^2 + (12 : ℝ) * ((a)) * (-b/2 - c/2 + 1)^2 + (12 : ℝ) * ((a) * (-a*b - a*c - b*c + 3)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a * b + a * c + b * c = 3), 8 * (a + b + c) ^ 2 ≥ 9 * (a + b) * (a + c) * (b + c)) := @solution
#print axioms solution
