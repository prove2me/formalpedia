-- Prove2me | solution 1 for UtilityTokens.ICOChoice.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T02:20:37.642413+00:00
-- url     : https://prove2.me/submissions/69c19937-15af-4bea-841c-9c69f89e2abb

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting

namespace Aux_UTICOp2
open UtilityTokens.ICOChoice

/-- the cubic `θ (Θ - θ) (Θ + 1 - θ)` in expanded form -/
def hc (Θ θ : ℝ) : ℝ := θ ^ 3 - (2 * Θ + 1) * θ ^ 2 + Θ * (Θ + 1) * θ

lemma hc_deriv (Θ θ : ℝ) :
    HasDerivAt (hc Θ) (3 * θ ^ 2 - 2 * (2 * Θ + 1) * θ + Θ * (Θ + 1)) θ := by
  have h := ((hasDerivAt_pow 3 θ).sub ((hasDerivAt_pow 2 θ).const_mul (2 * Θ + 1))).add
    ((hasDerivAt_id θ).const_mul (Θ * (Θ + 1)))
  refine h.congr_deriv ?_
  first | ring | (push_cast; ring) | (simp; ring)

lemma hc_cont (Θ : ℝ) : Continuous (hc Θ) := by unfold hc; fun_prop

lemma V_eq (Θ x f θ : ℝ) (hΘ : 0 < Θ) :
    (θ * ((Θ - θ) / Θ) ^ 2 + (1 - (Θ - θ) / Θ) * ((Θ - θ) / Θ)) * x - f =
      x * hc Θ θ / Θ ^ 2 - f := by
  unfold hc
  field_simp
  ring

/-- value of a choice is at most the value of choosing `p1 = u`. -/
lemma profit_le (Θ x f θ p1 : ℝ) (hΘ : 1 < Θ) (hx : 0 < x) (hθ1 : 1 ≤ θ) (hθΘ : θ ≤ Θ) :
    profitI Θ x f θ p1 ≤
      (θ * ((Θ - θ) / Θ) ^ 2 + (1 - (Θ - θ) / Θ) * ((Θ - θ) / Θ)) * x - f := by
  have hΘ0 : 0 < Θ := by linarith
  have ha0 : 0 ≤ (Θ - θ) / Θ := div_nonneg (by linarith) hΘ0.le
  have ha1 : (Θ - θ) / Θ ≤ 1 := by rw [div_le_one hΘ0]; linarith
  unfold profitI demandI1 demandI0 thresholdPrice basicUtility activeShare
  by_cases h1 : θ = 1
  · subst h1
    simp only [eq_self_iff_true, if_true, sub_self, ite_self, mul_zero, add_zero, mul_one]
    apply le_of_eq
    ring
  · simp only [if_neg h1]
    split_ifs with h2
    · rw [h2]; apply le_of_eq; ring
    · have : 0 ≤ (1 - (Θ - θ) / Θ) * ((Θ - θ) / Θ) * x :=
        mul_nonneg (mul_nonneg (by linarith) ha0) hx.le
      nlinarith

end Aux_UTICOp2

open UtilityTokens.ICOChoice Aux_UTICOp2 in
theorem solution (Θ x f : ℝ) (hΘ1 : 1 < Θ) (hx : 0 < x) :
    let θs := thetaStar Θ
    let XI := (θs * ((Θ - θs) / Θ) ^ 2 + (1 - (Θ - θs) / Θ) * ((Θ - θs) / Θ)) * x - f
    (1 ≤ θs ∧ θs ≤ Θ) ∧
    IsGreatest ((fun c : ℝ × ℝ => profitI Θ x f c.1 c.2) '' ICOChoices Θ x) XI ∧
    profitI Θ x f θs (basicUtility Θ x θs) = XI ∧
    (∀ c ∈ ICOChoices Θ x, profitI Θ x f c.1 c.2 = XI → c.1 = θs) ∧
    (thresholdPrice Θ x θs = θs * ((Θ - θs) / Θ * x) ∧
      basicUtility Θ x θs = (Θ - θs) / Θ * x) ∧
    optPayoffI Θ x f = XI := by
  intro θs XI
  have hΘ0 : 0 < Θ := by linarith
  set s := Real.sqrt (Θ ^ 2 + Θ + 1) with hs
  have hs2 : s ^ 2 = Θ ^ 2 + Θ + 1 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsgt : Θ - 1 < s := by nlinarith
  have hθI : thetaInterior Θ = (2 * Θ + 1 - s) / 3 := rfl
  have hθIle : thetaInterior Θ ≤ Θ := by rw [hθI]; linarith
  have hθs : θs = max 1 (thetaInterior Θ) := rfl
  have hθs1 : 1 ≤ θs := le_max_left _ _
  have hθsΘ : θs ≤ Θ := max_le hΘ1.le hθIle
  have hθsI : thetaInterior Θ ≤ θs := le_max_right _ _
  -- factorization of the derivative
  have hfac : ∀ y : ℝ, 3 * y ^ 2 - 2 * (2 * Θ + 1) * y + Θ * (Θ + 1) =
      3 * (y - (2 * Θ + 1 - s) / 3) * (y - (2 * Θ + 1 + s) / 3) := by
    intro y; nlinarith [hs2]
  have hmono : StrictMonoOn (hc Θ) (Set.Icc 1 θs) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (hc_cont Θ).continuousOn
    intro y hy
    rw [interior_Icc] at hy
    rw [(hc_deriv Θ y).deriv, hfac]
    have h1 : y < (2 * Θ + 1 - s) / 3 := by
      rcases le_total 1 (thetaInterior Θ) with h | h
      · have : θs = thetaInterior Θ := max_eq_right h
        rw [← hθI, ← this]; exact hy.2
      · have : θs = 1 := max_eq_left h
        rw [this] at hy; linarith [hy.1, hy.2]
    have h2 : y < (2 * Θ + 1 + s) / 3 := by linarith
    nlinarith
  have hanti : StrictAntiOn (hc Θ) (Set.Icc θs Θ) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (hc_cont Θ).continuousOn
    intro y hy
    rw [interior_Icc] at hy
    rw [(hc_deriv Θ y).deriv, hfac]
    have h1 : (2 * Θ + 1 - s) / 3 < y := by rw [← hθI]; linarith [hy.1]
    have h2 : y < (2 * Θ + 1 + s) / 3 := by linarith [hy.2]
    nlinarith
  -- value comparison
  have hVle : ∀ θ, 1 ≤ θ → θ ≤ Θ → hc Θ θ ≤ hc Θ θs ∧ (hc Θ θ = hc Θ θs → θ = θs) := by
    intro θ h1 h2
    rcases lt_trichotomy θ θs with h | h | h
    · have := hmono ⟨h1, h.le⟩ ⟨hθs1, le_rfl⟩ h
      exact ⟨this.le, fun he => absurd he this.ne⟩
    · exact ⟨by rw [h], fun _ => h⟩
    · have := hanti ⟨le_rfl, hθsΘ⟩ ⟨h.le, h2⟩ h
      exact ⟨this.le, fun he => absurd he this.ne⟩
  have hXI : XI = x * hc Θ θs / Θ ^ 2 - f := V_eq Θ x f θs hΘ0
  have hVθ : ∀ θ, 1 ≤ θ → θ ≤ Θ →
      (θ * ((Θ - θ) / Θ) ^ 2 + (1 - (Θ - θ) / Θ) * ((Θ - θ) / Θ)) * x - f ≤ XI ∧
      ((θ * ((Θ - θ) / Θ) ^ 2 + (1 - (Θ - θ) / Θ) * ((Θ - θ) / Θ)) * x - f = XI → θ = θs) := by
    intro θ h1 h2
    rw [V_eq Θ x f θ hΘ0, hXI]
    obtain ⟨hle, heq⟩ := hVle θ h1 h2
    have hΘ2 : 0 < Θ ^ 2 := by positivity
    refine ⟨?_, fun he => heq ?_⟩
    · have := mul_le_mul_of_nonneg_left hle hx.le
      have := div_le_div_of_nonneg_right this hΘ2.le
      linarith
    · have : x * hc Θ θ / Θ ^ 2 = x * hc Θ θs / Θ ^ 2 := by linarith
      rw [div_left_inj' (ne_of_gt hΘ2)] at this
      exact mul_left_cancel₀ hx.ne' this
  -- the optimal choice
  have hval : profitI Θ x f θs (basicUtility Θ x θs) = XI := by
    unfold profitI demandI1 demandI0 thresholdPrice
    show _ = (θs * ((Θ - θs) / Θ) ^ 2 + (1 - (Θ - θs) / Θ) * ((Θ - θs) / Θ)) * x - f
    unfold basicUtility activeShare
    by_cases h1 : θs = 1
    · rw [h1]; simp only [eq_self_iff_true, if_true, ite_true]; ring
    · simp only [if_neg h1, eq_self_iff_true, if_true, ite_true]; ring
  have hmem : (θs, basicUtility Θ x θs) ∈ ICOChoices Θ x := by
    refine ⟨⟨hθs1, hθsΘ⟩, le_rfl, ?_⟩
    show basicUtility Θ x θs ≤ Θ * basicUtility Θ x θs
    have : 0 ≤ basicUtility Θ x θs := by
      unfold basicUtility activeShare
      exact mul_nonneg (div_nonneg (by linarith) hΘ0.le) hx.le
    nlinarith
  have hgreat : IsGreatest ((fun c : ℝ × ℝ => profitI Θ x f c.1 c.2) '' ICOChoices Θ x) XI := by
    refine ⟨⟨_, hmem, hval⟩, ?_⟩
    rintro _ ⟨c, hc', rfl⟩
    obtain ⟨⟨h1, h2⟩, _⟩ := hc'
    exact (profit_le Θ x f c.1 c.2 hΘ1 hx h1 h2).trans (hVθ c.1 h1 h2).1
  refine ⟨⟨hθs1, hθsΘ⟩, hgreat, hval, ?_, ⟨rfl, rfl⟩, hgreat.csSup_eq⟩
  intro c hc' heq
  obtain ⟨⟨h1, h2⟩, _⟩ := hc'
  have hp := profit_le Θ x f c.1 c.2 hΘ1 hx h1 h2
  obtain ⟨hle, huniq⟩ := hVθ c.1 h1 h2
  apply huniq
  linarith
