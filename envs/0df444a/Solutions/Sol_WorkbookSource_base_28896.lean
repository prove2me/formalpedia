-- Prove2me | solution 1 for WorkbookSource.base_28896
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:12:29.857276+00:00
-- url     : https://prove2.me/submissions/0949fc1a-e3f9-4715-a31a-7b2f6da72fba

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution  (x y : ℝ)
  (h₀ : 5 * x^2 - 4 * x * y - y^2 = 5) :
  2 * x^2 + y^2 ≥ 5 / 3  := by
  have hw0 : 0 ≤ (5*x^2 - 4*x*y - y^2 - 5) := by linarith only [h₀]
  have hw1 : 0 ≤ (-5*x^2 + 4*x*y + y^2 + 5) := by linarith only [h₀]
  have hsum : 0 ≤ (4/3 : ℝ) * (1) * (x/2 + y)^2 + (1/3 : ℝ) * ((5*x^2 - 4*x*y - y^2 - 5)) * (1)^2 := by positivity
  have hid : (
  2 * x^2 + y^2 ) - ( 5 / 3  ) = (4/3 : ℝ) * (1) * (x/2 + y)^2 + (1/3 : ℝ) * ((5*x^2 - 4*x*y - y^2 - 5)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (x y : ℝ)
  (h₀ : 5 * x^2 - 4 * x * y - y^2 = 5), 2 * x^2 + y^2 ≥ 5 / 3) := @solution
#print axioms solution
