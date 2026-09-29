-- Prove2me | solution 1 for WorkbookSource.plus_51590
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:41.638749+00:00
-- url     : https://prove2.me/submissions/9bd24ea9-6a71-47ea-ac6e-8d0612e26d3a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2) (hc : c ≤ 1 / 2) (habc : a + b + c = 1) : a^2 + b^2 + c^2 + 9 * a * b * c ≥ 2 * (a * b + b * c + c * a)   := by
  have hw0 : 0 ≤ (1/2 - a) := by linarith only [ha]
  have hw1 : 0 ≤ (1/2 - b) := by linarith only [hb]
  have hw2 : 0 ≤ (1/2 - c) := by linarith only [hc]
  have hw3 : 0 ≤ (a + b + c - 1) := by linarith only [habc]
  have hw4 : 0 ≤ (-a - b - c + 1) := by linarith only [habc]
  have hsum : 0 ≤ (1/3 : ℝ) * ((-a - b - c + 1)) * (-a/2 - b/2 + c)^2 + (1/4 : ℝ) * ((-a - b - c + 1)) * (-a + b)^2 + (1/3 : ℝ) * ((a + b + c - 1)) * (a + b + c)^2 + (1 : ℝ) * ((1/2 - c)) * (-a + b)^2 + (1 : ℝ) * ((1/2 - b)) * (-a + c)^2 + (1 : ℝ) * ((1/2 - a)) * (-b + c)^2 := by positivity
  have hid : ( a^2 + b^2 + c^2 + 9 * a * b * c ) - ( 2 * (a * b + b * c + c * a)   ) = (1/3 : ℝ) * ((-a - b - c + 1)) * (-a/2 - b/2 + c)^2 + (1/4 : ℝ) * ((-a - b - c + 1)) * (-a + b)^2 + (1/3 : ℝ) * ((a + b + c - 1)) * (a + b + c)^2 + (1 : ℝ) * ((1/2 - c)) * (-a + b)^2 + (1 : ℝ) * ((1/2 - b)) * (-a + c)^2 + (1 : ℝ) * ((1/2 - a)) * (-b + c)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a ≤ 1 / 2) (hb : b ≤ 1 / 2) (hc : c ≤ 1 / 2) (habc : a + b + c = 1), a^2 + b^2 + c^2 + 9 * a * b * c ≥ 2 * (a * b + b * c + c * a)) := @solution
#print axioms solution
