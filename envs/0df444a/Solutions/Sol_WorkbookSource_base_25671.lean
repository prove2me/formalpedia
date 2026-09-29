-- Prove2me | solution 1 for WorkbookSource.base_25671
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:44:16.991569+00:00
-- url     : https://prove2.me/submissions/bd1560fd-a67a-414a-b69f-ca3175ed3902

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x - y) / (x * y + 2 * y + 1) + (y - z) / (y * z + 2 * z + 1) + (z - x) / (z * x + 2 * x + 1) ≥ 0  := by
  have hn : 0 ≤ (2*x^2*y^2 - 2*x^2*y*z - x^2*y + 2*x^2*z^2 + 5*x^2*z + 2*x^2 - 2*x*y^2*z + 5*x*y^2 - 2*x*y*z^2 - 12*x*y*z - 2*x*y - x*z^2 - 2*x*z + 2*y^2*z^2 - y^2*z + 2*y^2 + 5*y*z^2 - 2*y*z + 2*z^2) := by
    have hs0 : 0 ≤ (2 : ℝ) * (1) * (-x*y/2 - x*z/2 - x/2 + y*z - y/2 + z)^2 := by positivity
    have hs1 : 0 ≤ (3/2 : ℝ) * (1) * (x*y - x*z - x + y)^2 := by positivity
    have hs2 : 0 ≤ (1 : ℝ) * (z) * (-x + y)^2 := by positivity
    have hs3 : 0 ≤ (1 : ℝ) * (y) * (-x + z)^2 := by positivity
    have hs4 : 0 ≤ (1 : ℝ) * (x) * (-y + z)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4]
  have hd : 0 < ((x*y + 2*y + 1)*(x*z + 2*x + 1)*(y*z + 2*z + 1)) := by positivity
  have heqrat : ( (x - y) / (x * y + 2 * y + 1) + (y - z) / (y * z + 2 * z + 1) + (z - x) / (z * x + 2 * x + 1) ) - ( 0  ) = (2*x^2*y^2 - 2*x^2*y*z - x^2*y + 2*x^2*z^2 + 5*x^2*z + 2*x^2 - 2*x*y^2*z + 5*x*y^2 - 2*x*y*z^2 - 12*x*y*z - 2*x*y - x*z^2 - 2*x*z + 2*y^2*z^2 - y^2*z + 2*y^2 + 5*y*z^2 - 2*y*z + 2*z^2) / ((x*y + 2*y + 1)*(x*z + 2*x + 1)*(y*z + 2*z + 1)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x - y) / (x * y + 2 * y + 1) + (y - z) / (y * z + 2 * z + 1) + (z - x) / (z * x + 2 * x + 1) ≥ 0) := @solution
#print axioms solution
