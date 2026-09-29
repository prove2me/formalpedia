-- Prove2me | solution 1 for WorkbookSource.base_53090
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:46:22.809808+00:00
-- url     : https://prove2.me/submissions/6586f742-f500-4e39-aa4d-1f60488504ba

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a^2 + b^2 + c^2 + 1 ≥ 4 * (a * b + b * c + c * a)  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a + b + c - 1) := by linarith only [habc]
  have hw4 : 0 ≤ (-a - b - c + 1) := by linarith only [habc]
  have hsum : 0 ≤ (2 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (3/2 : ℝ) * (1) * (-a + b)^2 + (2 : ℝ) * ((-a - b - c + 1)) * (1)^2 + (1 : ℝ) * ((a + b + c - 1) * (-a - b - c + 1)) * (1)^2 := by positivity
  have hid : ( a^2 + b^2 + c^2 + 1 ) - ( 4 * (a * b + b * c + c * a)  ) = (2 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (3/2 : ℝ) * (1) * (-a + b)^2 + (2 : ℝ) * ((-a - b - c + 1)) * (1)^2 + (1 : ℝ) * ((a + b + c - 1) * (-a - b - c + 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1), a^2 + b^2 + c^2 + 1 ≥ 4 * (a * b + b * c + c * a)) := @solution
#print axioms solution
