-- Prove2me | solution 1 for WorkbookSource.plus_10275
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:46:25.548268+00:00
-- url     : https://prove2.me/submissions/2ecf9d7c-291a-4d67-9d65-35d637fbde12

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = a^2 + b^2 + c^2) : a^3 + b^3 + c^3 + 3 * (a * b + b * c + c * a) ≤ 12   := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (-a^2 + a - b^2 + b - c^2 + c) := by linarith only [hab]
  have hw4 : 0 ≤ (a^2 - a + b^2 - b + c^2 - c) := by linarith only [hab]
  have hsum : 0 ≤ (12 : ℝ) * (1) * (-a/3 - b/3 - c/3 + 1)^2 + (11/3 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (11/4 : ℝ) * (1) * (-a + b)^2 + (6 : ℝ) * ((-a^2 + a - b^2 + b - c^2 + c)) * (1)^2 + (2 : ℝ) * ((c)) * (-a/2 - b/2 + 1)^2 + (1/2 : ℝ) * ((c)) * (-a + b)^2 + (1 : ℝ) * ((c) * (-a^2 + a - b^2 + b - c^2 + c)) * (1)^2 + (2 : ℝ) * ((b)) * (-a/2 - c/2 + 1)^2 + (1/2 : ℝ) * ((b)) * (-a + c)^2 + (1 : ℝ) * ((b) * (-a^2 + a - b^2 + b - c^2 + c)) * (1)^2 + (2 : ℝ) * ((a)) * (-b/2 - c/2 + 1)^2 + (1/2 : ℝ) * ((a)) * (-b + c)^2 + (1 : ℝ) * ((a) * (-a^2 + a - b^2 + b - c^2 + c)) * (1)^2 := by positivity
  have hid : ( 12   ) - ( a^3 + b^3 + c^3 + 3 * (a * b + b * c + c * a) ) = (12 : ℝ) * (1) * (-a/3 - b/3 - c/3 + 1)^2 + (11/3 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (11/4 : ℝ) * (1) * (-a + b)^2 + (6 : ℝ) * ((-a^2 + a - b^2 + b - c^2 + c)) * (1)^2 + (2 : ℝ) * ((c)) * (-a/2 - b/2 + 1)^2 + (1/2 : ℝ) * ((c)) * (-a + b)^2 + (1 : ℝ) * ((c) * (-a^2 + a - b^2 + b - c^2 + c)) * (1)^2 + (2 : ℝ) * ((b)) * (-a/2 - c/2 + 1)^2 + (1/2 : ℝ) * ((b)) * (-a + c)^2 + (1 : ℝ) * ((b) * (-a^2 + a - b^2 + b - c^2 + c)) * (1)^2 + (2 : ℝ) * ((a)) * (-b/2 - c/2 + 1)^2 + (1/2 : ℝ) * ((a)) * (-b + c)^2 + (1 : ℝ) * ((a) * (-a^2 + a - b^2 + b - c^2 + c)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = a^2 + b^2 + c^2), a^3 + b^3 + c^3 + 3 * (a * b + b * c + c * a) ≤ 12) := @solution
#print axioms solution
