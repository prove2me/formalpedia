-- Prove2me | solution 1 for OutcomeRebate.Transfer.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T20:48:37.017091+00:00
-- url     : https://prove2.me/submissions/b046cc92-2c6a-43bd-9997-a1313af758ae

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Theorems.Thm_OutcomeRebate_Transfer_closed_forms_outcome

namespace OutcomeRebate.Transfer

lemma obp_p2_diff (P : Params) (hS : P.Standing) (p : ℝ) (hp : 0 ≤ p) (hpv : p ≤ P.vbar) :
    payerObjO P P.β p - payerObjO P 1 p =
      P.n * P.q / P.vbar * ((1 - P.β) * p * (P.vp - (1 - P.β) * p / 2)) := by
  have hβ := hS.2.2.2.1
  have hβh := hS.2.2.2.2.1
  rw [(closed_forms_outcome P hS P.β p (Or.inl rfl) hp).2,
    (closed_forms_outcome P hS 1 p (Or.inr rfl) hp).2]
  have h1 : max (P.vbar - P.β * p) 0 = P.vbar - P.β * p := by
    apply max_eq_left; nlinarith
  have h2 : max (P.vbar - 1 * p) 0 = P.vbar - 1 * p := by
    apply max_eq_left; linarith
  rw [h1, h2]; ring

end OutcomeRebate.Transfer

open OutcomeRebate.Transfer

theorem solution (P : Params) (hS : P.Standing) :
    (∀ p : ℝ, P.vbar / P.β ≤ p → payerObjO P 1 p = payerObjO P P.β p) ∧
    (∀ p : ℝ, 0 ≤ p → p < P.vbar / P.β →
      (p ≤ P.vbar → (coversO P p ↔ p ≤ 2 * P.vp / (1 - P.β))) ∧
      (P.vbar < p → (coversO P p ↔ p ≤ (P.vp + P.vbar / 2) / (1 - P.β / 2)))) := by
  have hS' := hS
  obtain ⟨hn, hv, hc, hβ, hβh, hq0, hqlt, hα0, hα1, hlam, hvp⟩ := hS'
  have hvβ : P.vbar ≤ P.vbar / P.β := by
    rw [le_div_iff₀ hβ]; nlinarith
  have hN : 0 < P.n * P.q / P.vbar := by positivity
  refine ⟨fun p hp => ?_, fun p hp0 hp => ⟨fun hpv => ?_, fun hpv => ?_⟩⟩
  · have hp0 : 0 ≤ p := le_trans (div_pos hv hβ).le hp
    rw [(closed_forms_outcome P hS P.β p (Or.inl rfl) hp0).2,
      (closed_forms_outcome P hS 1 p (Or.inr rfl) hp0).2]
    rw [div_le_iff₀ hβ] at hp
    have h1 : max (P.vbar - P.β * p) 0 = 0 := by apply max_eq_right; linarith
    have h2 : max (P.vbar - 1 * p) 0 = 0 := by apply max_eq_right; nlinarith
    rw [h1, h2]; simp
  · unfold coversO
    rw [← sub_nonneg, obp_p2_diff P hS p hp0 hpv]
    have h1β : 0 < 1 - P.β := by linarith
    rw [le_div_iff₀ h1β]
    constructor
    · intro h
      have h' : 0 ≤ (1 - P.β) * p * (P.vp - (1 - P.β) * p / 2) := by
        by_contra hc'
        push Not at hc'
        have := mul_neg_of_pos_of_neg hN hc'
        linarith
      rcases eq_or_lt_of_le hp0 with h0 | h0
      · rw [← h0]; linarith
      · have : 0 ≤ P.vp - (1 - P.β) * p / 2 := by
          by_contra hc'
          push Not at hc'
          have := mul_neg_of_pos_of_neg (mul_pos h1β h0) hc'
          linarith
        linarith
    · intro h
      apply mul_nonneg hN.le
      apply mul_nonneg (mul_nonneg h1β.le hp0)
      linarith
  · unfold coversO
    rw [(closed_forms_outcome P hS P.β p (Or.inl rfl) hp0).2,
      (closed_forms_outcome P hS 1 p (Or.inr rfl) hp0).2]
    have hp' : P.β * p < P.vbar := by rwa [lt_div_iff₀ hβ, mul_comm] at hp
    have h1 : max (P.vbar - P.β * p) 0 = P.vbar - P.β * p := by apply max_eq_left; linarith
    have h2 : max (P.vbar - 1 * p) 0 = 0 := by apply max_eq_right; linarith
    rw [h1, h2]
    simp only [mul_zero, zero_mul]
    have h2β : 0 < 1 - P.β / 2 := by linarith
    rw [le_div_iff₀ h2β]
    have hpos : 0 < P.n * P.q / P.vbar * (P.vbar - P.β * p) := mul_pos hN (by linarith)
    constructor
    · intro h
      have : 0 ≤ P.vp - p + (P.vbar + P.β * p) / 2 := by
        by_contra hc'
        push Not at hc'
        have := mul_neg_of_pos_of_neg hpos hc'
        linarith
      linarith
    · intro h
      apply mul_nonneg hpos.le
      linarith
