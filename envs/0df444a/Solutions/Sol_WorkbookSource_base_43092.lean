-- Prove2me | solution 1 for WorkbookSource.base_43092
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:45:31.076973+00:00
-- url     : https://prove2.me/submissions/64aeb0cd-fdc5-435a-ba2c-88e0fa16ad57

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x y d : ℝ) (h₁ : x^2 - y^2 = 9 - 4*y) (h₂ : d^2 = x^2 + y^2): d^2 ≥ 7  := by
  have hw0 : 0 ≤ (x^2 - y^2 + 4*y - 9) := by linarith only [h₁]
  have hw1 : 0 ≤ (-x^2 + y^2 - 4*y + 9) := by linarith only [h₁]
  have hw2 : 0 ≤ (d^2 - x^2 - y^2) := by linarith only [h₂]
  have hw3 : 0 ≤ (-d^2 + x^2 + y^2) := by linarith only [h₂]
  have hsum : 0 ≤ (2 : ℝ) * (1) * (1 - y)^2 + (1 : ℝ) * ((d^2 - x^2 - y^2)) * (1)^2 + (1 : ℝ) * ((x^2 - y^2 + 4*y - 9)) * (1)^2 := by positivity
  have hid : ( d^2 ) - ( 7  ) = (2 : ℝ) * (1) * (1 - y)^2 + (1 : ℝ) * ((d^2 - x^2 - y^2)) * (1)^2 + (1 : ℝ) * ((x^2 - y^2 + 4*y - 9)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y d : ℝ) (h₁ : x^2 - y^2 = 9 - 4*y) (h₂ : d^2 = x^2 + y^2), d^2 ≥ 7) := @solution
#print axioms solution
