-- Prove2me | solution 1 for WorkbookSource.plus_73118
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:44.76964+00:00
-- url     : https://prove2.me/submissions/83426bc2-d694-411a-9937-b3f5c1650298

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c = a * b * c + 3) : a ^ 3 + b ^ 3 + c ^ 3 ≥ 27 / 4   := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (-a*b*c + a + b + c - 3) := by linarith only [habc]
  have hw4 : 0 ≤ (a*b*c - a - b - c + 3) := by linarith only [habc]
  have hsum : 0 ≤ (27/2 : ℝ) * (1) * (-a/3 - b/3 - c/3 + 1)^2 + (27/4 : ℝ) * ((-a*b*c + a + b + c - 3)) * (1)^2 + (9/4 : ℝ) * ((c)) * (-a/3 - b/3 - c/3 + 1)^2 + (3/4 : ℝ) * ((c)) * (-a - b + c)^2 + (9/4 : ℝ) * ((b)) * (-a/3 - b/3 - c/3 + 1)^2 + (3/4 : ℝ) * ((b)) * (a - b + c)^2 + (9/4 : ℝ) * ((a)) * (-a/3 - b/3 - c/3 + 1)^2 + (3/4 : ℝ) * ((a)) * (-a + b + c)^2 + (3/4 : ℝ) * ((a) * (b) * (c)) * (1)^2 := by positivity
  have hid : ( a ^ 3 + b ^ 3 + c ^ 3 ) - ( 27 / 4   ) = (27/2 : ℝ) * (1) * (-a/3 - b/3 - c/3 + 1)^2 + (27/4 : ℝ) * ((-a*b*c + a + b + c - 3)) * (1)^2 + (9/4 : ℝ) * ((c)) * (-a/3 - b/3 - c/3 + 1)^2 + (3/4 : ℝ) * ((c)) * (-a - b + c)^2 + (9/4 : ℝ) * ((b)) * (-a/3 - b/3 - c/3 + 1)^2 + (3/4 : ℝ) * ((b)) * (a - b + c)^2 + (9/4 : ℝ) * ((a)) * (-a/3 - b/3 - c/3 + 1)^2 + (3/4 : ℝ) * ((a)) * (-a + b + c)^2 + (3/4 : ℝ) * ((a) * (b) * (c)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c = a * b * c + 3), a ^ 3 + b ^ 3 + c ^ 3 ≥ 27 / 4) := @solution
#print axioms solution
