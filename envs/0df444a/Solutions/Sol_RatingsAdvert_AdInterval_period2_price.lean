-- Prove2me | solution 1 for RatingsAdvert.AdInterval.period2_price
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:26:53.119217+00:00
-- url     : https://prove2.me/submissions/0c2eaaae-1661-468d-b7dd-d01089a99979

import Mathlib
import Definitions.Def_RatingsAdvert_AdInterval_Model

namespace Aux_RatingsAdvert_period2

theorem quad_max (c p : ℝ) : (∀ p' : ℝ, p' * (c - p') ≤ p * (c - p)) ↔ p = c / 2 := by
  constructor
  · intro h
    have h1 := h (c / 2)
    have h2 : (p - c / 2) ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
    have h3 : p - c / 2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    linarith
  · rintro rfl p'
    nlinarith [sq_nonneg (p' - c / 2)]

end Aux_RatingsAdvert_period2

open RatingsAdvert.AdInterval in
theorem solution (P : Params) (x p : ℝ) :
    ((∀ p' : ℝ, p' * D2Bench P p' ≤ p * D2Bench P p) ↔ p = (1 + P.beta - P.tau) / 2) ∧
      ((∀ p' : ℝ, p' * D2Info P x p' ≤ p * D2Info P x p) ↔
        p = (1 + P.beta * x - P.tau) / 2) := by
  have e1 : ∀ p', D2Bench P p' = (1 + P.beta - P.tau) - p' := fun p' => by
    unfold D2Bench; ring
  have e2 : ∀ p', D2Info P x p' = (1 + P.beta * x - P.tau) - p' := fun p' => by
    unfold D2Info; ring
  simp only [e1, e2]
  exact ⟨Aux_RatingsAdvert_period2.quad_max _ _, Aux_RatingsAdvert_period2.quad_max _ _⟩
