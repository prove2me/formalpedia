-- Prove2me | solution 1 for WorkbookSource.base_33501
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:45:21.867258+00:00
-- url     : https://prove2.me/submissions/81aeeab7-69cc-403b-9ecc-be5d906be24e

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) : a^2 + b^2 + c^2 ≥ a * b * c + (a + b) * (b + c) * (c + a)  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (a + b + c - 1) := by linarith only [habc]
  have hw4 : 0 ≤ (-a - b - c + 1) := by linarith only [habc]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (3/4 : ℝ) * (1) * (-a + b)^2 + (1/3 : ℝ) * ((-a - b - c + 1)) * (a + b + c)^2 + (1/3 : ℝ) * ((a + b + c - 1)) * (-a/2 - b/2 + c)^2 + (1/4 : ℝ) * ((a + b + c - 1)) * (-a + b)^2 := by positivity
  have hid : ( a^2 + b^2 + c^2 ) - ( a * b * c + (a + b) * (b + c) * (c + a)  ) = (1 : ℝ) * (1) * (-a/2 - b/2 + c)^2 + (3/4 : ℝ) * (1) * (-a + b)^2 + (1/3 : ℝ) * ((-a - b - c + 1)) * (a + b + c)^2 + (1/3 : ℝ) * ((a + b + c - 1)) * (-a/2 - b/2 + c)^2 + (1/4 : ℝ) * ((a + b + c - 1)) * (-a + b)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1), a^2 + b^2 + c^2 ≥ a * b * c + (a + b) * (b + c) * (c + a)) := @solution
#print axioms solution
