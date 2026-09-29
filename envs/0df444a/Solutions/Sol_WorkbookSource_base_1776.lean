-- Prove2me | solution 1 for WorkbookSource.base_1776
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:11:10.370975+00:00
-- url     : https://prove2.me/submissions/5d5e9929-2a62-459b-9f6a-8f65a4cfaaee

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (h1 : a^2 + b^2 = 1/2) (h2 : c * d = 1) : (a - d)^2 + (b - c)^2 ≥ 1/2  := by
  have hw0 : 0 ≤ (a^2 + b^2 - 1/2) := by linarith only [h1]
  have hw1 : 0 ≤ (-a^2 - b^2 + 1/2) := by linarith only [h1]
  have hw2 : 0 ≤ (c*d - 1) := by linarith only [h2]
  have hw3 : 0 ≤ (-c*d + 1) := by linarith only [h2]
  have hsum : 0 ≤ (2 : ℝ) * (1) * (b - c/2)^2 + (2 : ℝ) * (1) * (a - d/2)^2 + (1/2 : ℝ) * (1) * (-c + d)^2 + (1 : ℝ) * ((c*d - 1)) * (1)^2 + (1 : ℝ) * ((-a^2 - b^2 + 1/2)) * (1)^2 := by positivity
  have hid : ( (a - d)^2 + (b - c)^2 ) - ( 1/2  ) = (2 : ℝ) * (1) * (b - c/2)^2 + (2 : ℝ) * (1) * (a - d/2)^2 + (1/2 : ℝ) * (1) * (-c + d)^2 + (1 : ℝ) * ((c*d - 1)) * (1)^2 + (1 : ℝ) * ((-a^2 - b^2 + 1/2)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (h1 : a^2 + b^2 = 1/2) (h2 : c * d = 1), (a - d)^2 + (b - c)^2 ≥ 1/2) := @solution
#print axioms solution
