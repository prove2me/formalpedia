-- Prove2me | solution 1 for WorkbookSource.base_29461
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:30.502235+00:00
-- url     : https://prove2.me/submissions/9813c1bf-37c0-4d9a-92e4-3a308df4b509

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a * b + 2 * b * c + 3 * a * c ≤ 3 / 4  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a + b + c - 1) := by linarith only [habc]
  have hw4 : 0 ≤ (-a - b - c + 1) := by linarith only [habc]
  have hsum : 0 ≤ (9/10 : ℝ) * (1) * (-7*a/9 - b/3 + c - 1/9)^2 + (2/5 : ℝ) * (1) * (-a/3 + b + 1/6)^2 + (1/9 : ℝ) * (1) * (a - 1/2)^2 + (6/5 : ℝ) * ((-a - b - c + 1)) * (1)^2 + (1/2 : ℝ) * ((a + b + c - 1) * (-a - b - c + 1)) * (1)^2 + (2/5 : ℝ) * ((c) * (-a - b - c + 1)) * (1)^2 + (1/5 : ℝ) * ((a) * (-a - b - c + 1)) * (1)^2 := by positivity
  have hid : ( 3 / 4  ) - ( a * b + 2 * b * c + 3 * a * c ) = (9/10 : ℝ) * (1) * (-7*a/9 - b/3 + c - 1/9)^2 + (2/5 : ℝ) * (1) * (-a/3 + b + 1/6)^2 + (1/9 : ℝ) * (1) * (a - 1/2)^2 + (6/5 : ℝ) * ((-a - b - c + 1)) * (1)^2 + (1/2 : ℝ) * ((a + b + c - 1) * (-a - b - c + 1)) * (1)^2 + (2/5 : ℝ) * ((c) * (-a - b - c + 1)) * (1)^2 + (1/5 : ℝ) * ((a) * (-a - b - c + 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1), a * b + 2 * b * c + 3 * a * c ≤ 3 / 4) := @solution
#print axioms solution
