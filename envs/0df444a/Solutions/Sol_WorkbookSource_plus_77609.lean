-- Prove2me | solution 1 for WorkbookSource.plus_77609
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:55:36.437089+00:00
-- url     : https://prove2.me/submissions/42e5b1e5-78a3-46f9-ad94-cee2a78a93f5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2*x + 4*y + 3)*(2*y + 4*z + 3)*(2*z + 4*x + 3) / (x*y + y*z + z*x) ≥ 243   := by
  have hn : 0 ≤ (16*x^2*y + 32*x^2*z + 24*x^2 + 32*x*y^2 + 72*x*y*z - 159*x*y + 16*x*z^2 - 159*x*z + 54*x + 16*y^2*z + 24*y^2 + 32*y*z^2 - 159*y*z + 54*y + 24*z^2 + 54*z + 27) := by
    have hs0 : 0 ≤ (27 : ℝ) * (1) * (-x/3 - y/3 - z/3 + 1)^2 := by positivity
    have hs1 : 0 ≤ (21 : ℝ) * (1) * (-x/2 - y/2 + z)^2 := by positivity
    have hs2 : 0 ≤ (63/4 : ℝ) * (1) * (-x + y)^2 := by positivity
    have hs3 : 0 ≤ (72 : ℝ) * (z) * (-11*x/18 - 7*y/18 + 1)^2 := by positivity
    have hs4 : 0 ≤ (46/9 : ℝ) * (z) * (-x + y)^2 := by positivity
    have hs5 : 0 ≤ (72 : ℝ) * (y) * (-7*x/18 - 11*z/18 + 1)^2 := by positivity
    have hs6 : 0 ≤ (46/9 : ℝ) * (y) * (-x + z)^2 := by positivity
    have hs7 : 0 ≤ (72 : ℝ) * (x) * (-11*y/18 - 7*z/18 + 1)^2 := by positivity
    have hs8 : 0 ≤ (46/9 : ℝ) * (x) * (-y + z)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8]
  have hd : (0 : ℝ) < (x*y + x*z + y*z) := by positivity
  have heqrat : ( (2*x + 4*y + 3)*(2*y + 4*z + 3)*(2*z + 4*x + 3) / (x*y + y*z + z*x) ) - ( 243   ) = (16*x^2*y + 32*x^2*z + 24*x^2 + 32*x*y^2 + 72*x*y*z - 159*x*y + 16*x*z^2 - 159*x*z + 54*x + 16*y^2*z + 24*y^2 + 32*y*z^2 - 159*y*z + 54*y + 24*z^2 + 54*z + 27) / (x*y + x*z + y*z) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (2*x + 4*y + 3)*(2*y + 4*z + 3)*(2*z + 4*x + 3) / (x*y + y*z + z*x) ≥ 243) := @solution
#print axioms solution
