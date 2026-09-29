-- Prove2me | solution 1 for WorkbookSource.base_12296
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:44:21.303704+00:00
-- url     : https://prove2.me/submissions/898330a3-eeb4-40cc-ba84-db7a288d60db

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1) :
  a * (1 + d - a) + b * (1 + d - b) + c * (1 + d - c) - d - 1 ≤ 0  := by
  have hw0 : 0 ≤ (a^2 + b^2 + c^2 + d^2 - 1) := by linarith only [h]
  have hw1 : 0 ≤ (-a^2 - b^2 - c^2 - d^2 + 1) := by linarith only [h]
  have hsum : 0 ≤ (3/2 : ℝ) * (1) * (c - d/3 - 1/3)^2 + (3/2 : ℝ) * (1) * (b - d/3 - 1/3)^2 + (3/2 : ℝ) * (1) * (a - d/3 - 1/3)^2 + (1/2 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1)) * (1)^2 := by positivity
  have hid : ( 0  ) - (
  a * (1 + d - a) + b * (1 + d - b) + c * (1 + d - c) - d - 1 ) = (3/2 : ℝ) * (1) * (c - d/3 - 1/3)^2 + (3/2 : ℝ) * (1) * (b - d/3 - 1/3)^2 + (3/2 : ℝ) * (1) * (a - d/3 - 1/3)^2 + (1/2 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 1), a * (1 + d - a) + b * (1 + d - b) + c * (1 + d - c) - d - 1 ≤ 0) := @solution
#print axioms solution
