-- Prove2me | solution 1 for WorkbookSource.base_26343
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:09:42.208449+00:00
-- url     : https://prove2.me/submissions/1f57c625-22af-42f9-8586-502130aa6285

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : (a / (a + 1) / (b + 1) + b / (b + 1) / (c + 1) + c / (c + 1) / (a + 1)) ≥ 3 / 4  := by
  have hproduct_aux : (∀ (a b : ℝ) (ha : 0 < a) (hb : 0 < b), (a / (a + 1) / (b + 1) + b / (b + 1) / (((1) / (a * b)) + 1) + ((1) / (a * b)) / (((1) / (a * b)) + 1) / (a + 1)) ≥ 3 / 4) := by
    intro a b ha hb
    have hn : 0 ≤ (a^2*b^2 + a^2*b + a*b^2 - 6*a*b + a + b + 1) := by
      have hs0 : 0 ≤ (1 : ℝ) * (1) * (-a*b + 1)^2 := by positivity
      have hs1 : 0 ≤ (1 : ℝ) * (b) * (1 - a)^2 := by positivity
      have hs2 : 0 ≤ (1 : ℝ) * (a) * (1 - b)^2 := by positivity
      nlinarith only [hs0, hs1, hs2]
    have hd : (0 : ℝ) < (4*(a + 1)*(b + 1)*(a*b + 1)) := by positivity
    have heqrat : (  (a / (a + 1) / (b + 1) + b / (b + 1) / (((1) / (a * b)) + 1) + ((1) / (a * b)) / (((1) / (a * b)) + 1) / (a + 1)) ) - ( 3 / 4   ) = (a^2*b^2 + a^2*b + a*b^2 - 6*a*b + a + b + 1) / (4*(a + 1)*(b + 1)*(a*b + 1)) := by
      field_simp (disch := positivity)
      <;> ring
    have hp := div_nonneg hn (le_of_lt hd)
    linarith only [heqrat, hp]
  have hproduct_elim : c = ((1) / (a * b)) := by
    apply (eq_div_iff (by positivity)).2
    nlinarith only [habc]
  simpa only [hproduct_elim] using (hproduct_aux a b (by simpa only [hproduct_elim] using ha) (by simpa only [hproduct_elim] using hb))
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1), (a / (a + 1) / (b + 1) + b / (b + 1) / (c + 1) + c / (c + 1) / (a + 1)) ≥ 3 / 4) := @solution
#print axioms solution
