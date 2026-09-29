-- Prove2me | solution 1 for WorkbookSource.plus_15135
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:37.858345+00:00
-- url     : https://prove2.me/submissions/850be068-e654-45d2-ab57-0547d38dbc24

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c = 3) : a^2 + (1 / 2) * b^2 + c^2 + a * b + c * a ≥ 3   := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a + b + c - 3) := by linarith only [habc]
  have hw4 : 0 ≤ (-a - b - c + 3) := by linarith only [habc]
  have hsum : 0 ≤ (2/3 : ℝ) * (1) * (a/4 - b/2 + c)^2 + (5/8 : ℝ) * (1) * (a)^2 + (1 : ℝ) * ((a + b + c - 3)) * (1)^2 + (1/3 : ℝ) * ((c) * (a + b + c - 3)) * (1)^2 + (1/3 : ℝ) * ((b) * (a + b + c - 3)) * (1)^2 + (1/3 : ℝ) * ((a) * (a + b + c - 3)) * (1)^2 + (1/2 : ℝ) * ((a) * (b)) * (1)^2 := by positivity
  have hid : ( a^2 + (1 / 2) * b^2 + c^2 + a * b + c * a ) - ( 3   ) = (2/3 : ℝ) * (1) * (a/4 - b/2 + c)^2 + (5/8 : ℝ) * (1) * (a)^2 + (1 : ℝ) * ((a + b + c - 3)) * (1)^2 + (1/3 : ℝ) * ((c) * (a + b + c - 3)) * (1)^2 + (1/3 : ℝ) * ((b) * (a + b + c - 3)) * (1)^2 + (1/3 : ℝ) * ((a) * (a + b + c - 3)) * (1)^2 + (1/2 : ℝ) * ((a) * (b)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (habc : a + b + c = 3), a^2 + (1 / 2) * b^2 + c^2 + a * b + c * a ≥ 3) := @solution
#print axioms solution
