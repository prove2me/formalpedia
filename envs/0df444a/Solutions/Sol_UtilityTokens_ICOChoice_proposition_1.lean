-- Prove2me | solution 1 for UtilityTokens.ICOChoice.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:28:08.613912+00:00
-- url     : https://prove2.me/submissions/e00f9d02-547e-4a25-b1bf-961edfc24d30

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting
set_option autoImplicit false

open UtilityTokens.ICOChoice

lemma uu_profit_one (Θ x : ℝ) : profitT Θ x 1 = (Θ - 1) / Θ * x := by
  unfold profitT thresholdPrice demandT basicUtility activeShare
  simp

lemma uu_profit_lt (Θ x θ : ℝ) (hΘ1 : 1 < Θ) (hΘ3 : Θ ≤ 3) (hx : 0 < x)
    (hθ1 : 1 < θ) (hθΘ : θ ≤ Θ) : profitT Θ x θ < (Θ - 1) / Θ * x := by
  unfold profitT thresholdPrice demandT basicUtility activeShare
  rw [if_neg hθ1.ne']
  have hΘ : 0 < Θ := by linarith
  have key : θ * (Θ - θ) ^ 2 < Θ * (Θ - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hθ1.le) (sub_nonneg.2 hθΘ), sq_nonneg (θ - 1),
      mul_nonneg (sub_nonneg.2 hθ1.le) (sub_nonneg.2 (by linarith : Θ ≤ 3)),
      mul_nonneg (sub_nonneg.2 hθ1.le) (sub_nonneg.2 hθΘ), mul_pos (sub_pos.2 hθ1) (sub_pos.2 hΘ1)]
  have : θ * ((Θ - θ) / Θ * x) * ((Θ - θ) / Θ) = (θ * (Θ - θ) ^ 2) / Θ ^ 2 * x := by
    field_simp
  rw [this]
  have h2 : (θ * (Θ - θ) ^ 2) / Θ ^ 2 < (Θ - 1) / Θ := by
    rw [div_lt_div_iff₀ (by positivity) hΘ]
    nlinarith [key]
  have := mul_lt_mul_of_pos_right h2 hx
  linarith

theorem solution (Θ x : ℝ) (hΘ1 : 1 < Θ) (hΘ3 : Θ ≤ 3) (hx : 0 < x) :
    IsGreatest (profitT Θ x '' Set.Icc 1 Θ) ((Θ - 1) / Θ * x) ∧
    (∀ θbar ∈ Set.Icc 1 Θ, profitT Θ x θbar = (Θ - 1) / Θ * x → θbar = 1) ∧
    thresholdPrice Θ x 1 = (Θ - 1) / Θ * x ∧
    optPayoffT Θ x = (Θ - 1) / Θ * x := by
  have hG : IsGreatest (profitT Θ x '' Set.Icc 1 Θ) ((Θ - 1) / Θ * x) := by
    refine ⟨⟨1, ⟨le_rfl, hΘ1.le⟩, uu_profit_one Θ x⟩, ?_⟩
    rintro _ ⟨θ, hθ, rfl⟩
    rcases eq_or_lt_of_le hθ.1 with h | h
    · rw [← h, uu_profit_one]
    · exact (uu_profit_lt Θ x θ hΘ1 hΘ3 hx h hθ.2).le
  refine ⟨hG, ?_, ?_, ?_⟩
  · intro θ hθ heq
    by_contra hne
    have h1 : 1 < θ := lt_of_le_of_ne hθ.1 (Ne.symm hne)
    have := uu_profit_lt Θ x θ hΘ1 hΘ3 hx h1 hθ.2
    linarith
  · unfold thresholdPrice basicUtility activeShare; ring
  · unfold optPayoffT; exact hG.csSup_eq
