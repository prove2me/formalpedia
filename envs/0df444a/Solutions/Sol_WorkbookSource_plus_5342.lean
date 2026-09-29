-- Prove2me | solution 1 for WorkbookSource.plus_5342
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:47:33.86456+00:00
-- url     : https://prove2.me/submissions/683f58ef-5e86-4d88-ae31-f19edfe3cf61

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d k : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (h : a^2 + b^2 + c^2 + d^2 = 1) : 4 * (k - a) * (k - b) ≥ (c + d)^2 + 2 * (k^2 - 1)   := by
  have hw0 : 0 ≤ (a) := by linarith only [ha]
  have hw1 : 0 ≤ (b) := by linarith only [hb]
  have hw2 : 0 ≤ (c) := by linarith only [hc]
  have hw3 : 0 ≤ (d) := by linarith only [hd]
  have hw4 : 0 ≤ (a^2 + b^2 + c^2 + d^2 - 1) := by linarith only [h]
  have hw5 : 0 ≤ (-a^2 - b^2 - c^2 - d^2 + 1) := by linarith only [h]
  have hsum : 0 ≤ (2 : ℝ) * (1) * (-a - b + k)^2 + (1 : ℝ) * (1) * (-c + d)^2 + (2 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1)) * (1)^2 := by positivity
  have hid : ( 4 * (k - a) * (k - b) ) - ( (c + d)^2 + 2 * (k^2 - 1)   ) = (2 : ℝ) * (1) * (-a - b + k)^2 + (1 : ℝ) * (1) * (-c + d)^2 + (2 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d k : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (h : a^2 + b^2 + c^2 + d^2 = 1), 4 * (k - a) * (k - b) ≥ (c + d)^2 + 2 * (k^2 - 1)) := @solution
#print axioms solution
