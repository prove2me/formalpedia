-- Prove2me | solution 1 for WorkbookSource.base_52401
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:46:22.153622+00:00
-- url     : https://prove2.me/submissions/100e19c2-7d6e-47e4-adeb-560eabf05428

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a = 3) : a^2 + b^2 + c^2 + 2 * a * b * c + 3 ≥ (1 + a) * (1 + b) * (1 + c)  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a*b + a*c + b*c - 3) := by linarith only [hab]
  have hw4 : 0 ≤ (-a*b - a*c - b*c + 3) := by linarith only [hab]
  have hsum : 0 ≤ (5 : ℝ) * (1) * (-a/3 - b/3 - c/3 + 1)^2 + (4/9 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (1/3 : ℝ) * (1) * (-a + b)^2 + (1 : ℝ) * ((a*b + a*c + b*c - 3)) * (1)^2 + (4/3 : ℝ) * ((c)) * (-a/2 - b/2 + 1)^2 + (1/3 : ℝ) * ((c) * (-a*b - a*c - b*c + 3)) * (1)^2 + (4/3 : ℝ) * ((b)) * (-a/2 - c/2 + 1)^2 + (1/3 : ℝ) * ((b) * (-a*b - a*c - b*c + 3)) * (1)^2 + (4/3 : ℝ) * ((a)) * (-b/2 - c/2 + 1)^2 + (1/3 : ℝ) * ((a) * (-a*b - a*c - b*c + 3)) * (1)^2 := by positivity
  have hid : ( a^2 + b^2 + c^2 + 2 * a * b * c + 3 ) - ( (1 + a) * (1 + b) * (1 + c)  ) = (5 : ℝ) * (1) * (-a/3 - b/3 - c/3 + 1)^2 + (4/9 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (1/3 : ℝ) * (1) * (-a + b)^2 + (1 : ℝ) * ((a*b + a*c + b*c - 3)) * (1)^2 + (4/3 : ℝ) * ((c)) * (-a/2 - b/2 + 1)^2 + (1/3 : ℝ) * ((c) * (-a*b - a*c - b*c + 3)) * (1)^2 + (4/3 : ℝ) * ((b)) * (-a/2 - c/2 + 1)^2 + (1/3 : ℝ) * ((b) * (-a*b - a*c - b*c + 3)) * (1)^2 + (4/3 : ℝ) * ((a)) * (-b/2 - c/2 + 1)^2 + (1/3 : ℝ) * ((a) * (-a*b - a*c - b*c + 3)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a = 3), a^2 + b^2 + c^2 + 2 * a * b * c + 3 ≥ (1 + a) * (1 + b) * (1 + c)) := @solution
#print axioms solution
