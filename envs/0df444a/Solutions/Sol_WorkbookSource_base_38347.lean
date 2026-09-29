-- Prove2me | solution 1 for WorkbookSource.base_38347
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:45:27.426268+00:00
-- url     : https://prove2.me/submissions/78766141-f987-404a-93e7-e1d9b7a00c8a

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a = 3) : 3 * (a + b + c) + a * b * c ≥ 10  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a*b + a*c + b*c - 3) := by linarith only [hab]
  have hw4 : 0 ≤ (-a*b - a*c - b*c + 3) := by linarith only [hab]
  have hsum : 0 ≤ (10/3 : ℝ) * ((a*b + a*c + b*c - 3)) * (1)^2 + (5/3 : ℝ) * ((c)) * (-a/2 - b/2 + 1)^2 + (1/36 : ℝ) * ((c)) * (-a + b)^2 + (4/9 : ℝ) * ((c) * (-a*b - a*c - b*c + 3)) * (1)^2 + (5/3 : ℝ) * ((b)) * (-a/2 - c/2 + 1)^2 + (1/36 : ℝ) * ((b)) * (-a + c)^2 + (4/9 : ℝ) * ((b) * (-a*b - a*c - b*c + 3)) * (1)^2 + (5/3 : ℝ) * ((a)) * (-b/2 - c/2 + 1)^2 + (1/36 : ℝ) * ((a)) * (-b + c)^2 + (4/9 : ℝ) * ((a) * (-a*b - a*c - b*c + 3)) * (1)^2 := by positivity
  have hid : ( 3 * (a + b + c) + a * b * c ) - ( 10  ) = (10/3 : ℝ) * ((a*b + a*c + b*c - 3)) * (1)^2 + (5/3 : ℝ) * ((c)) * (-a/2 - b/2 + 1)^2 + (1/36 : ℝ) * ((c)) * (-a + b)^2 + (4/9 : ℝ) * ((c) * (-a*b - a*c - b*c + 3)) * (1)^2 + (5/3 : ℝ) * ((b)) * (-a/2 - c/2 + 1)^2 + (1/36 : ℝ) * ((b)) * (-a + c)^2 + (4/9 : ℝ) * ((b) * (-a*b - a*c - b*c + 3)) * (1)^2 + (5/3 : ℝ) * ((a)) * (-b/2 - c/2 + 1)^2 + (1/36 : ℝ) * ((a)) * (-b + c)^2 + (4/9 : ℝ) * ((a) * (-a*b - a*c - b*c + 3)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a = 3), 3 * (a + b + c) + a * b * c ≥ 10) := @solution
#print axioms solution
