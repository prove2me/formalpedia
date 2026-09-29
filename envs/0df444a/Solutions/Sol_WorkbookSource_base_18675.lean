-- Prove2me | solution 1 for WorkbookSource.base_18675
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:23:24.772008+00:00
-- url     : https://prove2.me/submissions/f17ba99b-8b0a-4a90-b643-7d0e8175b34e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = a * b * c) : a * (1 - b ^ 2) * (1 - c ^ 2) + b * (1 - c ^ 2) * (1 - a ^ 2) + c * (1 - a ^ 2) * (1 - b ^ 2) ≤ (4 / 27) * (a + b + c) ^ 3  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (-a*b*c + a + b + c) := by linarith only [habc]
  have hw4 : 0 ≤ (a*b*c - a - b - c) := by linarith only [habc]
  have hsum : 0 ≤ (1 : ℝ) * ((a*b*c - a - b - c)) * (1)^2 + (5/27 : ℝ) * ((a*b*c - a - b - c)) * (-a/2 - b/2 + c)^2 + (5/36 : ℝ) * ((a*b*c - a - b - c)) * (-a + b)^2 + (1/3 : ℝ) * ((-a*b*c + a + b + c)) * (a + b + c)^2 + (4/9 : ℝ) * ((c)) * (-a + b)^2 + (4/9 : ℝ) * ((b)) * (-a + c)^2 + (4/9 : ℝ) * ((a)) * (-b + c)^2 + (4/27 : ℝ) * ((a) * (b) * (c)) * (-a/2 - b/2 + c)^2 + (1/9 : ℝ) * ((a) * (b) * (c)) * (-a + b)^2 := by positivity
  have hid : ( (4 / 27) * (a + b + c) ^ 3  ) - ( a * (1 - b ^ 2) * (1 - c ^ 2) + b * (1 - c ^ 2) * (1 - a ^ 2) + c * (1 - a ^ 2) * (1 - b ^ 2) ) = (1 : ℝ) * ((a*b*c - a - b - c)) * (1)^2 + (5/27 : ℝ) * ((a*b*c - a - b - c)) * (-a/2 - b/2 + c)^2 + (5/36 : ℝ) * ((a*b*c - a - b - c)) * (-a + b)^2 + (1/3 : ℝ) * ((-a*b*c + a + b + c)) * (a + b + c)^2 + (4/9 : ℝ) * ((c)) * (-a + b)^2 + (4/9 : ℝ) * ((b)) * (-a + c)^2 + (4/9 : ℝ) * ((a)) * (-b + c)^2 + (4/27 : ℝ) * ((a) * (b) * (c)) * (-a/2 - b/2 + c)^2 + (1/9 : ℝ) * ((a) * (b) * (c)) * (-a + b)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = a * b * c), a * (1 - b ^ 2) * (1 - c ^ 2) + b * (1 - c ^ 2) * (1 - a ^ 2) + c * (1 - a ^ 2) * (1 - b ^ 2) ≤ (4 / 27) * (a + b + c) ^ 3) := @solution
#print axioms solution
