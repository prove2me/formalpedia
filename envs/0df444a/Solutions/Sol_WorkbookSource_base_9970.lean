-- Prove2me | solution 1 for WorkbookSource.base_9970
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:46:45.358417+00:00
-- url     : https://prove2.me/submissions/c8e08010-2645-4d0b-8e07-40a5e7346eb9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 16 / (x + y) + (x ^ 2 + 14 * x * y + y ^ 2 + 16) / (x * y) ≥ 80 / (x * y + 1)  := by
  have hn : 0 ≤ (x^4*y + 15*x^3*y^2 + x^3 + 15*x^2*y^3 + 16*x^2*y^2 - 49*x^2*y + x*y^4 - 49*x*y^2 + 16*x*y + 16*x + y^3 + 16*y) := by
    have hs0 : 0 ≤ (16 : ℝ) * (1) * (x*y - x/2 - y/2)^2 := by positivity
    have hs1 : 0 ≤ (16 : ℝ) * (y) * (-x^2/8 - 7*x*y/8 + x/8 - y/8 + 1)^2 := by positivity
    have hs2 : 0 ≤ (3/4 : ℝ) * (y) * (x^2 - x*y - x + y)^2 := by positivity
    have hs3 : 0 ≤ (16 : ℝ) * (x) * (-7*x*y/8 - x/8 - y^2/8 + y/8 + 1)^2 := by positivity
    have hs4 : 0 ≤ (3/4 : ℝ) * (x) * (x*y - x - y^2 + y)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  field_simp (disch := positivity)
  nlinarith only [hn]
example : (∀ (x y : ℝ) (hx : 0 < x) (hy : 0 < y), 16 / (x + y) + (x ^ 2 + 14 * x * y + y ^ 2 + 16) / (x * y) ≥ 80 / (x * y + 1)) := @solution
#print axioms solution
