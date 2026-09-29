-- Prove2me | solution 1 for WorkbookSource.base_36367
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:34.452731+00:00
-- url     : https://prove2.me/submissions/43a9ead6-0d67-4f26-8e9a-0b78c2e5b731

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a * b + b * c + c * a = 1) : a ^ 2 + b ^ 2 + c ^ 2 + a * b * c * (a + b + c) ≥ 4 / 3  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a*b + a*c + b*c - 1) := by linarith only [hab]
  have hw4 : 0 ≤ (-a*b - a*c - b*c + 1) := by linarith only [hab]
  have hsum : 0 ≤ (2/3 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (1/2 : ℝ) * (1) * (-a + b)^2 + (4/9 : ℝ) * ((-a*b - a*c - b*c + 1)) * (-a/2 - b/2 + c)^2 + (1/3 : ℝ) * ((-a*b - a*c - b*c + 1)) * (-a + b)^2 + (4/3 : ℝ) * ((a*b + a*c + b*c - 1)) * (1)^2 + (1/9 : ℝ) * ((a*b + a*c + b*c - 1)) * (a + b + c)^2 + (1/3 : ℝ) * ((b) * (c)) * (-b + c)^2 + (1/3 : ℝ) * ((a) * (c)) * (-a + c)^2 + (1/3 : ℝ) * ((a) * (b)) * (-a + b)^2 := by positivity
  have hid : ( a ^ 2 + b ^ 2 + c ^ 2 + a * b * c * (a + b + c) ) - ( 4 / 3  ) = (2/3 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (1/2 : ℝ) * (1) * (-a + b)^2 + (4/9 : ℝ) * ((-a*b - a*c - b*c + 1)) * (-a/2 - b/2 + c)^2 + (1/3 : ℝ) * ((-a*b - a*c - b*c + 1)) * (-a + b)^2 + (4/3 : ℝ) * ((a*b + a*c + b*c - 1)) * (1)^2 + (1/9 : ℝ) * ((a*b + a*c + b*c - 1)) * (a + b + c)^2 + (1/3 : ℝ) * ((b) * (c)) * (-b + c)^2 + (1/3 : ℝ) * ((a) * (c)) * (-a + c)^2 + (1/3 : ℝ) * ((a) * (b)) * (-a + b)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a * b + b * c + c * a = 1), a ^ 2 + b ^ 2 + c ^ 2 + a * b * c * (a + b + c) ≥ 4 / 3) := @solution
#print axioms solution
