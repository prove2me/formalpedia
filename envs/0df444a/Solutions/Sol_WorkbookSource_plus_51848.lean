-- Prove2me | solution 1 for WorkbookSource.plus_51848
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:46:28.28844+00:00
-- url     : https://prove2.me/submissions/a63696eb-6718-4b1f-ad28-0c5b5187be78

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a ^ 3 + b ^ 3 + c ^ 3 + a * b + b * c + c * a ≥ 6   := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a + b + c - 3) := by linarith only [habc]
  have hw4 : 0 ≤ (-a - b - c + 3) := by linarith only [habc]
  have hsum : 0 ≤ (5/4 : ℝ) * ((a + b + c - 3)) * (a/3 + b/3 + c/3 + 1)^2 + (1/4 : ℝ) * ((a + b + c - 3) * (-a - b - c + 3)) * (1)^2 + (25/28 : ℝ) * ((c)) * (-2*a/5 - 2*b/5 + c - 1/5)^2 + (1/4 : ℝ) * ((c)) * (-a + b)^2 + (2/63 : ℝ) * ((c) * (a + b + c - 3) * (-a - b - c + 3)) * (1)^2 + (25/28 : ℝ) * ((b)) * (-2*a/5 + b - 2*c/5 - 1/5)^2 + (1/4 : ℝ) * ((b)) * (-a + c)^2 + (2/63 : ℝ) * ((b) * (a + b + c - 3) * (-a - b - c + 3)) * (1)^2 + (25/28 : ℝ) * ((a)) * (a - 2*b/5 - 2*c/5 - 1/5)^2 + (1/4 : ℝ) * ((a)) * (-b + c)^2 + (2/63 : ℝ) * ((a) * (a + b + c - 3) * (-a - b - c + 3)) * (1)^2 := by positivity
  have hid : ( a ^ 3 + b ^ 3 + c ^ 3 + a * b + b * c + c * a ) - ( 6   ) = (5/4 : ℝ) * ((a + b + c - 3)) * (a/3 + b/3 + c/3 + 1)^2 + (1/4 : ℝ) * ((a + b + c - 3) * (-a - b - c + 3)) * (1)^2 + (25/28 : ℝ) * ((c)) * (-2*a/5 - 2*b/5 + c - 1/5)^2 + (1/4 : ℝ) * ((c)) * (-a + b)^2 + (2/63 : ℝ) * ((c) * (a + b + c - 3) * (-a - b - c + 3)) * (1)^2 + (25/28 : ℝ) * ((b)) * (-2*a/5 + b - 2*c/5 - 1/5)^2 + (1/4 : ℝ) * ((b)) * (-a + c)^2 + (2/63 : ℝ) * ((b) * (a + b + c - 3) * (-a - b - c + 3)) * (1)^2 + (25/28 : ℝ) * ((a)) * (a - 2*b/5 - 2*c/5 - 1/5)^2 + (1/4 : ℝ) * ((a)) * (-b + c)^2 + (2/63 : ℝ) * ((a) * (a + b + c - 3) * (-a - b - c + 3)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3), a ^ 3 + b ^ 3 + c ^ 3 + a * b + b * c + c * a ≥ 6) := @solution
#print axioms solution
