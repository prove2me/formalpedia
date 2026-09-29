-- Prove2me | solution 1 for WorkbookSource.base_16123
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:45:12.010129+00:00
-- url     : https://prove2.me/submissions/5ce18407-ea9e-43f6-a32e-d7f08d885a1d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : 4 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 3 * (a ^ 3 + b ^ 3 + c ^ 3) + 1  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a + b + c - 1) := by linarith only [habc]
  have hw4 : 0 ≤ (-a - b - c + 1) := by linarith only [habc]
  have hsum : 0 ≤ (187/70 : ℝ) * ((-a - b - c + 1)) * (-93*a/187 - 93*b/187 + c)^2 + (376/187 : ℝ) * ((-a - b - c + 1)) * (-93*a/94 + b)^2 + (2/47 : ℝ) * ((-a - b - c + 1)) * (a)^2 + (1 : ℝ) * ((a + b + c - 1)) * (2*a/7 + 2*b/7 + 2*c/7 + 1)^2 + (9/490 : ℝ) * ((a + b + c - 1)) * (a + b + c)^2 + (1 : ℝ) * ((c)) * (-a + b)^2 + (3/7 : ℝ) * ((c) * (a + b + c - 1) * (-a - b - c + 1)) * (1)^2 + (1 : ℝ) * ((b)) * (-a + c)^2 + (3/7 : ℝ) * ((b) * (a + b + c - 1) * (-a - b - c + 1)) * (1)^2 + (1 : ℝ) * ((a)) * (-b + c)^2 + (3/7 : ℝ) * ((a) * (a + b + c - 1) * (-a - b - c + 1)) * (1)^2 := by positivity
  have hid : ( 4 * (a ^ 2 + b ^ 2 + c ^ 2) ) - ( 3 * (a ^ 3 + b ^ 3 + c ^ 3) + 1  ) = (187/70 : ℝ) * ((-a - b - c + 1)) * (-93*a/187 - 93*b/187 + c)^2 + (376/187 : ℝ) * ((-a - b - c + 1)) * (-93*a/94 + b)^2 + (2/47 : ℝ) * ((-a - b - c + 1)) * (a)^2 + (1 : ℝ) * ((a + b + c - 1)) * (2*a/7 + 2*b/7 + 2*c/7 + 1)^2 + (9/490 : ℝ) * ((a + b + c - 1)) * (a + b + c)^2 + (1 : ℝ) * ((c)) * (-a + b)^2 + (3/7 : ℝ) * ((c) * (a + b + c - 1) * (-a - b - c + 1)) * (1)^2 + (1 : ℝ) * ((b)) * (-a + c)^2 + (3/7 : ℝ) * ((b) * (a + b + c - 1) * (-a - b - c + 1)) * (1)^2 + (1 : ℝ) * ((a)) * (-b + c)^2 + (3/7 : ℝ) * ((a) * (a + b + c - 1) * (-a - b - c + 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1), 4 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 3 * (a ^ 3 + b ^ 3 + c ^ 3) + 1) := @solution
#print axioms solution
