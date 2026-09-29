-- Prove2me | solution 1 for WorkbookSource.plus_30516
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:39.11319+00:00
-- url     : https://prove2.me/submissions/605138cb-c53c-4132-af56-fe2e01d7bb57

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b : ℝ) (h : a^2 + b^2 = 1) : (a + 1) * (a + 2 * b + 1) ≤ 27 / 5   := by
  have hw0 : 0 ≤ (a^2 + b^2 - 1) := by linarith only [h]
  have hw1 : 0 ≤ (-a^2 - b^2 + 1) := by linarith only [h]
  have hsum : 0 ≤ (3 : ℝ) * (1) * (-a/3 + b - 1/3)^2 + (5/3 : ℝ) * (1) * (a - 4/5)^2 + (3 : ℝ) * ((-a^2 - b^2 + 1)) * (1)^2 := by positivity
  have hid : ( 27 / 5   ) - ( (a + 1) * (a + 2 * b + 1) ) = (3 : ℝ) * (1) * (-a/3 + b - 1/3)^2 + (5/3 : ℝ) * (1) * (a - 4/5)^2 + (3 : ℝ) * ((-a^2 - b^2 + 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b : ℝ) (h : a^2 + b^2 = 1), (a + 1) * (a + 2 * b + 1) ≤ 27 / 5) := @solution
#print axioms solution
