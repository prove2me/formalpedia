-- Prove2me | solution 1 for WorkbookSource.plus_27662
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:53:26.419283+00:00
-- url     : https://prove2.me/submissions/4ef79a8d-95d2-4097-8081-2bd72a36247c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 + y^2 + z^2) * (1 / x^2 + 1 / y^2 + 1 / z^2) ≥ 5 * (x + y + z) * (1 / x + 1 / y + 1 / z) - 73 / 2   := by
  have hn : 0 ≤ (2*x^4*y^2 + 2*x^4*z^2 - 10*x^3*y^2*z - 10*x^3*y*z^2 + 2*x^2*y^4 - 10*x^2*y^3*z + 49*x^2*y^2*z^2 - 10*x^2*y*z^3 + 2*x^2*z^4 - 10*x*y^3*z^2 - 10*x*y^2*z^3 + 2*y^4*z^2 + 2*y^2*z^4) := by
    have hs0 : 0 ≤ (49 : ℝ) * (1) * (-x^2*y/7 - x^2*z/7 - x*y^2/7 + x*y*z - x*z^2/7 - y^2*z/7 - y*z^2/7)^2 := by positivity
    have hs1 : 0 ≤ (1 : ℝ) * (1) * (-x^2*y + x^2*z + x*y^2 - x*z^2 - y^2*z + y*z^2)^2 := by positivity
    nlinarith only [hs0, hs1]
  have hd : (0 : ℝ) < (2*x^2*y^2*z^2) := by positivity
  have heqrat : ( (x^2 + y^2 + z^2) * (1 / x^2 + 1 / y^2 + 1 / z^2) ) - ( 5 * (x + y + z) * (1 / x + 1 / y + 1 / z) - 73 / 2   ) = (2*x^4*y^2 + 2*x^4*z^2 - 10*x^3*y^2*z - 10*x^3*y*z^2 + 2*x^2*y^4 - 10*x^2*y^3*z + 49*x^2*y^2*z^2 - 10*x^2*y*z^3 + 2*x^2*z^4 - 10*x*y^3*z^2 - 10*x*y^2*z^3 + 2*y^4*z^2 + 2*y^2*z^4) / (2*x^2*y^2*z^2) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x^2 + y^2 + z^2) * (1 / x^2 + 1 / y^2 + 1 / z^2) ≥ 5 * (x + y + z) * (1 / x + 1 / y + 1 / z) - 73 / 2) := @solution
#print axioms solution
