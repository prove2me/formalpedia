-- Prove2me | solution 1 for WorkbookSource.base_45572
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:45:36.810403+00:00
-- url     : https://prove2.me/submissions/148b2d59-d634-4970-9110-8908f9dab157

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3) : 1 / a + 1 / b + 1 / c + 48 * a * b * c / 25 ≥ 123 / 25  := by
  have hhom : 0 ≤ (25*a^5*b/81 + 25*a^5*c/81 + 100*a^4*b^2/81 - 16*a^4*b*c/9 + 100*a^4*c^2/81 + 50*a^3*b^3/27 - 557*a^3*b^2*c/81 - 557*a^3*b*c^2/81 + 50*a^3*c^3/27 + 100*a^2*b^4/81 - 557*a^2*b^3*c/81 + 286*a^2*b^2*c^2/9 - 557*a^2*b*c^3/81 + 100*a^2*c^4/81 + 25*a*b^5/81 - 16*a*b^4*c/9 - 557*a*b^3*c^2/81 - 557*a*b^2*c^3/81 - 16*a*b*c^4/9 + 25*a*c^5/81 + 25*b^5*c/81 + 100*b^4*c^2/81 + 50*b^3*c^3/27 + 100*b^2*c^4/81 + 25*b*c^5/81) := by
    have hs0 : 0 ≤ (289/81 : ℝ) * (b*c) * (-14*a^2/17 + a*b + a*c - 5*b^2/17 - 10*b*c/17 - 5*c^2/17)^2 := by positivity
    have hs1 : 0 ≤ (289/81 : ℝ) * (a*c) * (-5*a^2/17 + a*b - 10*a*c/17 - 14*b^2/17 + b*c - 5*c^2/17)^2 := by positivity
    have hs2 : 0 ≤ (289/81 : ℝ) * (a*b) * (-5*a^2/17 - 10*a*b/17 + a*c - 5*b^2/17 + b*c - 14*c^2/17)^2 := by positivity
    nlinarith only [hs0, hs1, hs2]
  have hehom : (48*a^2*b^2*c^2 - 123*a*b*c + 25*a*b + 25*a*c + 25*b*c) = (25*a^5*b/81 + 25*a^5*c/81 + 100*a^4*b^2/81 - 16*a^4*b*c/9 + 100*a^4*c^2/81 + 50*a^3*b^3/27 - 557*a^3*b^2*c/81 - 557*a^3*b*c^2/81 + 50*a^3*c^3/27 + 100*a^2*b^4/81 - 557*a^2*b^3*c/81 + 286*a^2*b^2*c^2/9 - 557*a^2*b*c^3/81 + 100*a^2*c^4/81 + 25*a*b^5/81 - 16*a*b^4*c/9 - 557*a*b^3*c^2/81 - 557*a*b^2*c^3/81 - 16*a*b*c^4/9 + 25*a*c^5/81 + 25*b^5*c/81 + 100*b^4*c^2/81 + 50*b^3*c^3/27 + 100*b^2*c^4/81 + 25*b*c^5/81) := by
    linear_combination (-25*a^4*b/81 - 25*a^4*c/81 - 25*a^3*b^2/27 + 194*a^3*b*c/81 - 25*a^3*b/27 - 25*a^3*c^2/27 - 25*a^3*c/27 - 25*a^2*b^3/27 + 146*a^2*b^2*c/27 - 50*a^2*b^2/27 + 146*a^2*b*c^2/27 + 244*a^2*b*c/27 - 25*a^2*b/9 - 25*a^2*c^3/27 - 50*a^2*c^2/27 - 25*a^2*c/9 - 25*a*b^4/81 + 194*a*b^3*c/81 - 25*a*b^3/27 + 146*a*b^2*c^2/27 + 244*a*b^2*c/27 - 25*a*b^2/9 + 194*a*b*c^3/81 + 244*a*b*c^2/27 + 98*a*b*c/3 - 25*a*b/3 - 25*a*c^4/81 - 25*a*c^3/27 - 25*a*c^2/9 - 25*a*c/3 - 25*b^4*c/81 - 25*b^3*c^2/27 - 25*b^3*c/27 - 25*b^2*c^3/27 - 50*b^2*c^2/27 - 25*b^2*c/9 - 25*b*c^4/81 - 25*b*c^3/27 - 25*b*c^2/9 - 25*b*c/3) * habc
  have hn : 0 ≤ (48*a^2*b^2*c^2 - 123*a*b*c + 25*a*b + 25*a*c + 25*b*c) := by linarith only [hhom, hehom]
  have hd : (0 : ℝ) < (25*a*b*c) := by positivity
  have heqrat : ( 1 / a + 1 / b + 1 / c + 48 * a * b * c / 25 ) - ( 123 / 25  ) = (48*a^2*b^2*c^2 - 123*a*b*c + 25*a*b + 25*a*c + 25*b*c) / (25*a*b*c) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3), 1 / a + 1 / b + 1 / c + 48 * a * b * c / 25 ≥ 123 / 25) := @solution
#print axioms solution
