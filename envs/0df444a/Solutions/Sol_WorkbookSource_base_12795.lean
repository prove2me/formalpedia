-- Prove2me | solution 1 for WorkbookSource.base_12795
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:47:32.330473+00:00
-- url     : https://prove2.me/submissions/c260d02e-37cf-4f29-86da-122db605119c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) : a * b * (a + b) ^ 2 + b * c * (b + c) ^ 2 + c * a * (c + a) ^ 2 ≥ 4 * a * b * c  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a + b + c - 1) := by linarith only [hab]
  have hw4 : 0 ≤ (-a - b - c + 1) := by linarith only [hab]
  have hsum : 0 ≤ (1 : ℝ) * ((c)) * (-a + b)^2 + (4/27 : ℝ) * ((c) * (-a - b - c + 1)) * (-a/2 - b/2 + c)^2 + (16/27 : ℝ) * ((c) * (a + b + c - 1)) * (-a/2 + b + c/4)^2 + (4/9 : ℝ) * ((c) * (a + b + c - 1)) * (a + c/2)^2 + (1 : ℝ) * ((b)) * (-a + c)^2 + (4/27 : ℝ) * ((b) * (-a - b - c + 1)) * (-a/2 + b - c/2)^2 + (16/27 : ℝ) * ((b) * (a + b + c - 1)) * (-a/2 + b/4 + c)^2 + (4/9 : ℝ) * ((b) * (a + b + c - 1)) * (a + b/2)^2 + (1 : ℝ) * ((a)) * (-b + c)^2 + (4/27 : ℝ) * ((a) * (-a - b - c + 1)) * (a - b/2 - c/2)^2 + (16/27 : ℝ) * ((a) * (a + b + c - 1)) * (a/4 - b/2 + c)^2 + (4/9 : ℝ) * ((a) * (a + b + c - 1)) * (a/2 + b)^2 := by positivity
  have hid : ( a * b * (a + b) ^ 2 + b * c * (b + c) ^ 2 + c * a * (c + a) ^ 2 ) - ( 4 * a * b * c  ) = (1 : ℝ) * ((c)) * (-a + b)^2 + (4/27 : ℝ) * ((c) * (-a - b - c + 1)) * (-a/2 - b/2 + c)^2 + (16/27 : ℝ) * ((c) * (a + b + c - 1)) * (-a/2 + b + c/4)^2 + (4/9 : ℝ) * ((c) * (a + b + c - 1)) * (a + c/2)^2 + (1 : ℝ) * ((b)) * (-a + c)^2 + (4/27 : ℝ) * ((b) * (-a - b - c + 1)) * (-a/2 + b - c/2)^2 + (16/27 : ℝ) * ((b) * (a + b + c - 1)) * (-a/2 + b/4 + c)^2 + (4/9 : ℝ) * ((b) * (a + b + c - 1)) * (a + b/2)^2 + (1 : ℝ) * ((a)) * (-b + c)^2 + (4/27 : ℝ) * ((a) * (-a - b - c + 1)) * (a - b/2 - c/2)^2 + (16/27 : ℝ) * ((a) * (a + b + c - 1)) * (a/4 - b/2 + c)^2 + (4/9 : ℝ) * ((a) * (a + b + c - 1)) * (a/2 + b)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1), a * b * (a + b) ^ 2 + b * c * (b + c) ^ 2 + c * a * (c + a) ^ 2 ≥ 4 * a * b * c) := @solution
#print axioms solution
