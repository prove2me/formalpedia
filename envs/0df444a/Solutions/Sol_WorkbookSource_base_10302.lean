-- Prove2me | solution 1 for WorkbookSource.base_10302
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T07:24:51.633745+00:00
-- url     : https://prove2.me/submissions/5a3133f5-89ea-4e5a-afe6-7ad3f24f6194

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c d : ℝ) (hab : 0 < a) (hbc : 0 < b) (hcd : 0 < c) (hda : 0 < d)  (habcd : a + b + c + d = 4) : 4 / (a * b * c * d) ≥ a / b + b / c + c / d + d / a  := by
  have hhom : 0 ≤ (a^4/64 + a^3*b/16 + a^3*c/16 + a^3*d/16 + 3*a^2*b^2/32 + 3*a^2*b*c/16 + 3*a^2*b*d/16 + 3*a^2*c^2/32 - 13*a^2*c*d/16 + 3*a^2*d^2/32 + a*b^3/16 + 3*a*b^2*c/16 - 13*a*b^2*d/16 - 13*a*b*c^2/16 + 3*a*b*c*d/8 + 3*a*b*d^2/16 + a*c^3/16 + 3*a*c^2*d/16 + 3*a*c*d^2/16 + a*d^3/16 + b^4/64 + b^3*c/16 + b^3*d/16 + 3*b^2*c^2/32 + 3*b^2*c*d/16 + 3*b^2*d^2/32 + b*c^3/16 + 3*b*c^2*d/16 - 13*b*c*d^2/16 + b*d^3/16 + c^4/64 + c^3*d/16 + 3*c^2*d^2/32 + c*d^3/16 + d^4/64) := by
    have hs0 : 0 ≤ (9/16 : ℝ) * (1) * (-a^2/6 - a*b/3 + a*c - a*d/3 - b^2/6 - b*c/3 + b*d - c^2/6 - c*d/3 - d^2/6)^2 := by positivity
    have hs1 : 0 ≤ (1/4 : ℝ) * (b*d) * (a - b - c + d)^2 := by positivity
    have hs2 : 0 ≤ (1/4 : ℝ) * (a*c) * (-a - b + c + d)^2 := by positivity
    nlinarith only [hs0, hs1, hs2]
  have hehom : (-a^2*c*d - a*b^2*d - a*b*c^2 - b*c*d^2 + 4) = (a^4/64 + a^3*b/16 + a^3*c/16 + a^3*d/16 + 3*a^2*b^2/32 + 3*a^2*b*c/16 + 3*a^2*b*d/16 + 3*a^2*c^2/32 - 13*a^2*c*d/16 + 3*a^2*d^2/32 + a*b^3/16 + 3*a*b^2*c/16 - 13*a*b^2*d/16 - 13*a*b*c^2/16 + 3*a*b*c*d/8 + 3*a*b*d^2/16 + a*c^3/16 + 3*a*c^2*d/16 + 3*a*c*d^2/16 + a*d^3/16 + b^4/64 + b^3*c/16 + b^3*d/16 + 3*b^2*c^2/32 + 3*b^2*c*d/16 + 3*b^2*d^2/32 + b*c^3/16 + 3*b*c^2*d/16 - 13*b*c*d^2/16 + b*d^3/16 + c^4/64 + c^3*d/16 + 3*c^2*d^2/32 + c*d^3/16 + d^4/64) := by
    linear_combination (-a^3/64 - 3*a^2*b/64 - 3*a^2*c/64 - 3*a^2*d/64 - a^2/16 - 3*a*b^2/64 - 3*a*b*c/32 - 3*a*b*d/32 - a*b/8 - 3*a*c^2/64 - 3*a*c*d/32 - a*c/8 - 3*a*d^2/64 - a*d/8 - a/4 - b^3/64 - 3*b^2*c/64 - 3*b^2*d/64 - b^2/16 - 3*b*c^2/64 - 3*b*c*d/32 - b*c/8 - 3*b*d^2/64 - b*d/8 - b/4 - c^3/64 - 3*c^2*d/64 - c^2/16 - 3*c*d^2/64 - c*d/8 - c/4 - d^3/64 - d^2/16 - d/4 - 1) * habcd
  have hn : 0 ≤ (-a^2*c*d - a*b^2*d - a*b*c^2 - b*c*d^2 + 4) := by linarith only [hhom, hehom]
  have hd : (0 : ℝ) < (a*b*c*d) := by positivity
  have heqrat : ( 4 / (a * b * c * d) ) - ( a / b + b / c + c / d + d / a  ) = (-a^2*c*d - a*b^2*d - a*b*c^2 - b*c*d^2 + 4) / (a*b*c*d) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c d : ℝ) (hab : 0 < a) (hbc : 0 < b) (hcd : 0 < c) (hda : 0 < d)  (habcd : a + b + c + d = 4), 4 / (a * b * c * d) ≥ a / b + b / c + c / d + d / a) := @solution
#print axioms solution
