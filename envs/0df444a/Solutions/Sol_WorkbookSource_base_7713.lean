-- Prove2me | solution 1 for WorkbookSource.base_7713
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:11:11.91671+00:00
-- url     : https://prove2.me/submissions/56c46445-98d1-4660-9e74-d44336691fcd

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (h₁ : a + b + c + d = 4) (h₂ : a^2 + b^2 + c^2 + d^2 = 18) : a * b - 2 * c * d ≤ 74 / 5  := by
  have hw0 : 0 ≤ (a + b + c + d - 4) := by linarith only [h₁]
  have hw1 : 0 ≤ (-a - b - c - d + 4) := by linarith only [h₁]
  have hw2 : 0 ≤ (a^2 + b^2 + c^2 + d^2 - 18) := by linarith only [h₂]
  have hw3 : 0 ≤ (-a^2 - b^2 - c^2 - d^2 + 18) := by linarith only [h₂]
  have hsum : 0 ≤ (16/5 : ℝ) * (1) * (-a/4 - b/4 - c/4 - d/4 + 1)^2 + (4/5 : ℝ) * (1) * (-a/4 - b/4 + c + d)^2 + (3/4 : ℝ) * (1) * (-a + b)^2 + (1 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 18)) * (1)^2 + (8/5 : ℝ) * ((a + b + c + d - 4)) * (1)^2 := by positivity
  have hid : ( 74 / 5  ) - ( a * b - 2 * c * d ) = (16/5 : ℝ) * (1) * (-a/4 - b/4 - c/4 - d/4 + 1)^2 + (4/5 : ℝ) * (1) * (-a/4 - b/4 + c + d)^2 + (3/4 : ℝ) * (1) * (-a + b)^2 + (1 : ℝ) * ((-a^2 - b^2 - c^2 - d^2 + 18)) * (1)^2 + (8/5 : ℝ) * ((a + b + c + d - 4)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (h₁ : a + b + c + d = 4) (h₂ : a^2 + b^2 + c^2 + d^2 = 18), a * b - 2 * c * d ≤ 74 / 5) := @solution
#print axioms solution
