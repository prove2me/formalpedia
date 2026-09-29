-- Prove2me | solution 1 for WorkbookSource.base_14624
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:46.015055+00:00
-- url     : https://prove2.me/submissions/cf926f7c-8954-4799-96ea-2cf31d0c7d61

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = a * b + b * c + c * a) : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 6 * (a + b + c - 3)  := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (-a*b - a*c + a - b*c + b + c) := by linarith only [habc]
  have hw4 : 0 ≤ (a*b + a*c - a + b*c - b - c) := by linarith only [habc]
  have hsum : 0 ≤ (18 : ℝ) * (1) * (-a/3 - b/3 - c/3 + 1)^2 + (6 : ℝ) * ((-a*b - a*c + a - b*c + b + c)) * (1)^2 := by positivity
  have hid : ( (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ) - ( 6 * (a + b + c - 3)  ) = (18 : ℝ) * (1) * (-a/3 - b/3 - c/3 + 1)^2 + (6 : ℝ) * ((-a*b - a*c + a - b*c + b + c)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = a * b + b * c + c * a), (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 6 * (a + b + c - 3)) := @solution
#print axioms solution
