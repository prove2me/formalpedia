-- Prove2me | solution 1 for WorkbookSource.base_2154
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:54.395587+00:00
-- url     : https://prove2.me/submissions/152fa3e9-8ac8-4670-8d18-16709aaa6bb5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : (x^2 / y^2 + y^2 / (x + y)^2 + (x + y)^2 / x^2) ≥ (10 * (x^4 + y^4 + (x + y)^4)) / (x^2 + y^2 + (x + y)^2)^2  := by
  have hn : 0 ≤ ((x^3 + x^2*y - 2*x*y^2 - y^3)^2) := by
    have hs0 : 0 ≤ (4 : ℝ) * (1) * (-x^3/2 - x^2*y/2 + x*y^2 + y^3/2)^2 := by positivity
    nlinarith only [hs0]
  have hd : 0 < (x^2*y^2*(x + y)^2 : ℝ) := by positivity
  have he : ( (x^2 / y^2 + y^2 / (x + y)^2 + (x + y)^2 / x^2) ) - ( (10 * (x^4 + y^4 + (x + y)^4)) / (x^2 + y^2 + (x + y)^2)^2  ) = ((x^3 + x^2*y - 2*x*y^2 - y^3)^2) / (x^2*y^2*(x + y)^2) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  rw [← he] at hp
  linarith only [hp]
example : (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), (x^2 / y^2 + y^2 / (x + y)^2 + (x + y)^2 / x^2) ≥ (10 * (x^4 + y^4 + (x + y)^4)) / (x^2 + y^2 + (x + y)^2)^2) := @solution
#print axioms solution
