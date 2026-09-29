-- Prove2me | solution 1 for WorkbookSource.plus_2356
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:46:23.565468+00:00
-- url     : https://prove2.me/submissions/55fa9df1-4399-48e8-aa42-92cdefd3d941

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1) : a * (2 * a + b + 1) ^ 2 + b * (2 * b + c + 1) ^ 2 + c * (2 * c + a + 1) ^ 2 ≥ 4   := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a + b + c - 1) := by linarith only [hab]
  have hw4 : 0 ≤ (-a - b - c + 1) := by linarith only [hab]
  have hsum : 0 ≤ (4 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (3 : ℝ) * (1) * (-a + b)^2 + (34/9 : ℝ) * ((a + b + c - 1)) * (15*a/34 + 15*b/34 + 15*c/34 + 1)^2 + (455/306 : ℝ) * ((a + b + c - 1)) * (-157*a/455 - 157*b/455 + c)^2 + (596/455 : ℝ) * ((a + b + c - 1)) * (-157*a/298 + b)^2 + (141/149 : ℝ) * ((a + b + c - 1)) * (a)^2 + (2/9 : ℝ) * ((a + b + c - 1) * (-a - b - c + 1)) * (1)^2 + (16/9 : ℝ) * ((c)) * (a/4 - b/2 + c - 1/4)^2 + (16/9 : ℝ) * ((b)) * (-a/2 + b + c/4 - 1/4)^2 + (16/9 : ℝ) * ((a)) * (a + b/4 - c/2 - 1/4)^2 := by positivity
  have hid : ( a * (2 * a + b + 1) ^ 2 + b * (2 * b + c + 1) ^ 2 + c * (2 * c + a + 1) ^ 2 ) - ( 4   ) = (4 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (3 : ℝ) * (1) * (-a + b)^2 + (34/9 : ℝ) * ((a + b + c - 1)) * (15*a/34 + 15*b/34 + 15*c/34 + 1)^2 + (455/306 : ℝ) * ((a + b + c - 1)) * (-157*a/455 - 157*b/455 + c)^2 + (596/455 : ℝ) * ((a + b + c - 1)) * (-157*a/298 + b)^2 + (141/149 : ℝ) * ((a + b + c - 1)) * (a)^2 + (2/9 : ℝ) * ((a + b + c - 1) * (-a - b - c + 1)) * (1)^2 + (16/9 : ℝ) * ((c)) * (a/4 - b/2 + c - 1/4)^2 + (16/9 : ℝ) * ((b)) * (-a/2 + b + c/4 - 1/4)^2 + (16/9 : ℝ) * ((a)) * (a + b/4 - c/2 - 1/4)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 1), a * (2 * a + b + 1) ^ 2 + b * (2 * b + c + 1) ^ 2 + c * (2 * c + a + 1) ^ 2 ≥ 4) := @solution
#print axioms solution
