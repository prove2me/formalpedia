-- Prove2me | solution 1 for WorkbookSource.base_28673
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T06:45:28.663365+00:00
-- url     : https://prove2.me/submissions/41794d1c-111e-47b8-a9a1-c02fe263af55

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + 2 * b) / c + (b + 2 * c) / a + (c + 2 * a) / b + 117 * (a * b + b * c + c * a) / (8 * (a ^ 2 + b ^ 2 + c ^ 2)) ≥ 89 / 4  := by
  have hn : 0 ≤ (8*a^4*b + 16*a^4*c + 16*a^3*b^2 - 178*a^3*b*c + 8*a^3*c^2 + 8*a^2*b^3 + 141*a^2*b^2*c + 141*a^2*b*c^2 + 16*a^2*c^3 + 16*a*b^4 - 178*a*b^3*c + 141*a*b^2*c^2 - 178*a*b*c^3 + 8*a*c^4 + 8*b^4*c + 16*b^3*c^2 + 8*b^2*c^3 + 16*b*c^4) := by
    have hs0 : 0 ≤ (142 : ℝ) * (c) * (-47*a^2/142 + a*b + 13*a*c/284 - 16*b^2/71 - 15*b*c/71)^2 := by positivity
    have hs1 : 0 ≤ (686/71 : ℝ) * (c) * (3*a^2/14 - 25*a*c/28 - 2*b^2/7 + b*c)^2 := by positivity
    have hs2 : 0 ≤ (142 : ℝ) * (b) * (-16*a^2/71 - 15*a*b/71 + a*c + 13*b*c/284 - 47*c^2/142)^2 := by positivity
    have hs3 : 0 ≤ (686/71 : ℝ) * (b) * (-2*a^2/7 + a*b - 25*b*c/28 + 3*c^2/14)^2 := by positivity
    have hs4 : 0 ≤ (142 : ℝ) * (a) * (13*a*b/284 - 15*a*c/71 - 47*b^2/142 + b*c - 16*c^2/71)^2 := by positivity
    have hs5 : 0 ≤ (686/71 : ℝ) * (a) * (-25*a*b/28 + a*c + 3*b^2/14 - 2*c^2/7)^2 := by positivity
    nlinarith only [hs0, hs1, hs2, hs3, hs4, hs5]
  have hd : (0 : ℝ) < (8*a*b*c*(a^2 + b^2 + c^2)) := by positivity
  have heqrat : ( (a + 2 * b) / c + (b + 2 * c) / a + (c + 2 * a) / b + 117 * (a * b + b * c + c * a) / (8 * (a ^ 2 + b ^ 2 + c ^ 2)) ) - ( 89 / 4  ) = (8*a^4*b + 16*a^4*c + 16*a^3*b^2 - 178*a^3*b*c + 8*a^3*c^2 + 8*a^2*b^3 + 141*a^2*b^2*c + 141*a^2*b*c^2 + 16*a^2*c^3 + 16*a*b^4 - 178*a*b^3*c + 141*a*b^2*c^2 - 178*a*b*c^3 + 8*a*c^4 + 8*b^4*c + 16*b^3*c^2 + 8*b^2*c^3 + 16*b*c^4) / (8*a*b*c*(a^2 + b^2 + c^2)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  linarith only [heqrat, hp]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c), (a + 2 * b) / c + (b + 2 * c) / a + (c + 2 * a) / b + 117 * (a * b + b * c + c * a) / (8 * (a ^ 2 + b ^ 2 + c ^ 2)) ≥ 89 / 4) := @solution
#print axioms solution
