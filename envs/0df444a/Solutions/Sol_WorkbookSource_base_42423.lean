-- Prove2me | solution 1 for WorkbookSource.base_42423
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:45:28.718983+00:00
-- url     : https://prove2.me/submissions/81ff4274-6f3c-43ad-a68d-e4157a1e54b6

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : 2 * (a^2 + b^2 + c^2) ≥ a^3 + b^3 + c^3 + 42 * a * b * c - 1  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a + b + c - 1) := by linarith only [habc]
  have hw4 : 0 ≤ (-a - b - c + 1) := by linarith only [habc]
  have hsum : 0 ≤ (2 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (3/2 : ℝ) * (1) * (-a + b)^2 + (16/15 : ℝ) * ((-a - b - c + 1)) * (a + b + c + 3/4)^2 + (2/5 : ℝ) * ((-a - b - c + 1)) * (1)^2 + (2/3 : ℝ) * ((a + b + c - 1)) * (-a/2 - b/2 + c)^2 + (1/2 : ℝ) * ((a + b + c - 1)) * (-a + b)^2 + (5 : ℝ) * ((c)) * (-a + b)^2 + (3/5 : ℝ) * ((c) * (a + b + c - 1) * (-a - b - c + 1)) * (1)^2 + (5 : ℝ) * ((b)) * (-a + c)^2 + (3/5 : ℝ) * ((b) * (a + b + c - 1) * (-a - b - c + 1)) * (1)^2 + (5 : ℝ) * ((a)) * (-b + c)^2 + (3/5 : ℝ) * ((a) * (a + b + c - 1) * (-a - b - c + 1)) * (1)^2 := by positivity
  have hid : ( 2 * (a^2 + b^2 + c^2) ) - ( a^3 + b^3 + c^3 + 42 * a * b * c - 1  ) = (2 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (3/2 : ℝ) * (1) * (-a + b)^2 + (16/15 : ℝ) * ((-a - b - c + 1)) * (a + b + c + 3/4)^2 + (2/5 : ℝ) * ((-a - b - c + 1)) * (1)^2 + (2/3 : ℝ) * ((a + b + c - 1)) * (-a/2 - b/2 + c)^2 + (1/2 : ℝ) * ((a + b + c - 1)) * (-a + b)^2 + (5 : ℝ) * ((c)) * (-a + b)^2 + (3/5 : ℝ) * ((c) * (a + b + c - 1) * (-a - b - c + 1)) * (1)^2 + (5 : ℝ) * ((b)) * (-a + c)^2 + (3/5 : ℝ) * ((b) * (a + b + c - 1) * (-a - b - c + 1)) * (1)^2 + (5 : ℝ) * ((a)) * (-b + c)^2 + (3/5 : ℝ) * ((a) * (a + b + c - 1) * (-a - b - c + 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1), 2 * (a^2 + b^2 + c^2) ≥ a^3 + b^3 + c^3 + 42 * a * b * c - 1) := @solution
#print axioms solution
