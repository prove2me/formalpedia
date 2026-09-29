-- Prove2me | solution 1 for WorkbookSource.base_15336
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:47.281935+00:00
-- url     : https://prove2.me/submissions/d49b2398-ed8c-476a-86b2-b5ce2d020e44

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a^3 + b^3 + c^3 + 6 * a * b * c ≤ a^2 + b^2 + c^2  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a + b + c - 1) := by linarith only [habc]
  have hw4 : 0 ≤ (-a - b - c + 1) := by linarith only [habc]
  have hsum : 0 ≤ (1 : ℝ) * ((-a - b - c + 1)) * (c)^2 + (1 : ℝ) * ((-a - b - c + 1)) * (b)^2 + (1 : ℝ) * ((-a - b - c + 1)) * (a)^2 + (1 : ℝ) * ((c)) * (-a + b)^2 + (1 : ℝ) * ((b)) * (-a + c)^2 + (1 : ℝ) * ((a)) * (-b + c)^2 := by positivity
  have hid : ( a^2 + b^2 + c^2  ) - ( a^3 + b^3 + c^3 + 6 * a * b * c ) = (1 : ℝ) * ((-a - b - c + 1)) * (c)^2 + (1 : ℝ) * ((-a - b - c + 1)) * (b)^2 + (1 : ℝ) * ((-a - b - c + 1)) * (a)^2 + (1 : ℝ) * ((c)) * (-a + b)^2 + (1 : ℝ) * ((b)) * (-a + c)^2 + (1 : ℝ) * ((a)) * (-b + c)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1), a^3 + b^3 + c^3 + 6 * a * b * c ≤ a^2 + b^2 + c^2) := @solution
#print axioms solution
