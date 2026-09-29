-- Prove2me | solution 1 for WorkbookSource.base_3932
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:41.678169+00:00
-- url     : https://prove2.me/submissions/a3dc4318-02e9-4bb2-8d26-725061a74bb4

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a = 3) : 2 + a * b * c ≤ a + b + c  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a*b + a*c + b*c - 3) := by linarith only [hab]
  have hw4 : 0 ≤ (-a*b - a*c - b*c + 3) := by linarith only [hab]
  have hsum : 0 ≤ (2/3 : ℝ) * ((a*b + a*c + b*c - 3)) * (1)^2 + (1/3 : ℝ) * ((c)) * (-a/2 - b/2 + 1)^2 + (5/36 : ℝ) * ((c)) * (-a + b)^2 + (2/9 : ℝ) * ((c) * (-a*b - a*c - b*c + 3)) * (1)^2 + (1/3 : ℝ) * ((b)) * (-a/2 - c/2 + 1)^2 + (5/36 : ℝ) * ((b)) * (-a + c)^2 + (2/9 : ℝ) * ((b) * (-a*b - a*c - b*c + 3)) * (1)^2 + (1/3 : ℝ) * ((a)) * (-b/2 - c/2 + 1)^2 + (5/36 : ℝ) * ((a)) * (-b + c)^2 + (2/9 : ℝ) * ((a) * (-a*b - a*c - b*c + 3)) * (1)^2 := by positivity
  have hid : ( a + b + c  ) - ( 2 + a * b * c ) = (2/3 : ℝ) * ((a*b + a*c + b*c - 3)) * (1)^2 + (1/3 : ℝ) * ((c)) * (-a/2 - b/2 + 1)^2 + (5/36 : ℝ) * ((c)) * (-a + b)^2 + (2/9 : ℝ) * ((c) * (-a*b - a*c - b*c + 3)) * (1)^2 + (1/3 : ℝ) * ((b)) * (-a/2 - c/2 + 1)^2 + (5/36 : ℝ) * ((b)) * (-a + c)^2 + (2/9 : ℝ) * ((b) * (-a*b - a*c - b*c + 3)) * (1)^2 + (1/3 : ℝ) * ((a)) * (-b/2 - c/2 + 1)^2 + (5/36 : ℝ) * ((a)) * (-b + c)^2 + (2/9 : ℝ) * ((a) * (-a*b - a*c - b*c + 3)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a * b + b * c + c * a = 3), 2 + a * b * c ≤ a + b + c) := @solution
#print axioms solution
