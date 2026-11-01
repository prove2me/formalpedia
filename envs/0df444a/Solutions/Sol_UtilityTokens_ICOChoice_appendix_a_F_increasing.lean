-- Prove2me | solution 1 for UtilityTokens.ICOChoice.appendix_a_F_increasing
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:47:16.848346+00:00
-- url     : https://prove2.me/submissions/129df144-3447-4dca-a65f-eaad07fd5630

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting
import Theorems.Thm_UtilityTokens_ICOChoice_lemma_1
import Theorems.Thm_UtilityTokens_ICOChoice_appendix_a_derivatives

open UtilityTokens.ICOChoice

lemma ico_aux_key (Θ : ℝ) (hΘ : thetaTilde < Θ) :
    0 < Θ ∧ 1 < thetaInterior Θ ∧ thetaInterior Θ < Θ ∧ Θ < (Θ - thetaInterior Θ) ^ 2 := by
  obtain ⟨_, ⟨h1T, _⟩, _, hgt, _⟩ := lemma_1
  have hT1 : 1 < Θ := lt_trans h1T hΘ
  have hΘ0 : 0 < Θ := by linarith
  have hstar1 : 1 < thetaStar Θ := hgt Θ hΘ
  have hI1 : 1 < thetaInterior Θ := by
    unfold thetaStar at hstar1
    rcases le_total 1 (thetaInterior Θ) with h | h
    · rw [max_eq_right h] at hstar1; exact hstar1
    · rw [max_eq_left h] at hstar1; linarith
  have hlt : thetaInterior Θ < Θ := by
    unfold thetaInterior
    nlinarith [Real.sqrt_nonneg (Θ ^ 2 + Θ + 1)]
  refine ⟨hΘ0, hI1, hlt, ?_⟩
  unfold thetaInterior
  unfold thetaTilde at hΘ
  set s := Real.sqrt (Θ ^ 2 + Θ + 1) with hs_def
  have hs2 : s ^ 2 = Θ ^ 2 + Θ + 1 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  set t := Real.sqrt Θ with ht_def
  have ht2 : t ^ 2 = Θ := Real.sq_sqrt hΘ0.le
  have ht0 : 0 < t := Real.sqrt_pos.mpr hΘ0
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h50 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg _
  have htphi : (1 + Real.sqrt 5) / 2 < t := by
    by_contra hc
    push Not at hc
    have : t ^ 2 ≤ ((1 + Real.sqrt 5) / 2) ^ 2 := pow_le_pow_left₀ ht0.le hc 2
    nlinarith
  have hq : 0 < t ^ 2 - t - 1 := by nlinarith
  have hslt : 3 * t + 1 - t ^ 2 < s := by
    by_contra hc
    push Not at hc
    have h' : s ^ 2 ≤ (3 * t + 1 - t ^ 2) ^ 2 := pow_le_pow_left₀ hs0 hc 2
    have : (3 * t + 1 - t ^ 2) ^ 2 = s ^ 2 - 6 * t * (t ^ 2 - t - 1) := by
      rw [hs2, ← ht2]; ring
    nlinarith [mul_pos ht0 hq]
  have hpos : 3 * t < Θ - 1 + s := by nlinarith
  have : Θ - (2 * Θ + 1 - s) / 3 = (Θ - 1 + s) / 3 := by ring
  rw [this]
  have h9 : 9 * Θ < (Θ - 1 + s) ^ 2 := by
    have := mul_lt_mul'' hpos hpos (by positivity) (by positivity)
    nlinarith
  nlinarith

lemma ico_aux_deriv (Θ : ℝ) (hΘ : thetaTilde < Θ) : ∃ d : ℝ, HasDerivAt Fden d Θ ∧ 0 < d := by
  obtain ⟨hΘ0, hI1, hlt, hsq⟩ := ico_aux_key Θ hΘ
  obtain ⟨hθ, hd'pos, -, hrat⟩ := appendix_a_derivatives Θ hΘ0
  set d' := 2 / 3 * (1 - (2 * Θ + 1) / (4 * Real.sqrt (Θ ^ 2 + Θ + 1))) with hd'
  have hG := (hθ.sub_const 1).mul
    ((((hasDerivAt_id Θ).sub hθ).div (hasDerivAt_id Θ) hΘ0.ne').pow 2 |>.sub
      ((hasDerivAt_const Θ (1:ℝ)).div (hasDerivAt_id Θ) hΘ0.ne'))
  have hev : Fden =ᶠ[nhds Θ]
      (fun y => (thetaInterior y - 1) *
        (((id y - thetaInterior y) / id y) ^ 2 - (fun _ => (1:ℝ)) y / id y)) := by
    have hc : ContinuousAt thetaInterior Θ := hθ.continuousAt
    have : ∀ᶠ y in nhds Θ, 1 < thetaInterior y :=
      hc.eventually (lt_mem_nhds hI1)
    filter_upwards [this] with y hy
    unfold Fden thetaStar
    rw [max_eq_right hy.le]
    simp
  refine ⟨_, hG.congr_of_eventuallyEq hev, ?_⟩
  simp only [Pi.sub_apply, Pi.div_apply, Pi.pow_apply, id]
  set θ := thetaInterior Θ
  have hB : 0 < ((Θ - θ) / Θ) ^ 2 - 1 / Θ := by
    have : ((Θ - θ) / Θ) ^ 2 - 1 / Θ = ((Θ - θ) ^ 2 - Θ) / Θ ^ 2 := by field_simp
    rw [this]; apply div_pos <;> nlinarith
  have hΘθ : 0 < Θ - θ := by linarith
  have hθd : 0 < θ - d' * Θ := by
    have := mul_pos hrat hΘ0
    have e : (θ / Θ - d') * Θ = θ - d' * Θ := by field_simp
    linarith
  have e2 : ((1 - d') * Θ - (Θ - θ) * 1) / Θ ^ 2 = (θ - d' * Θ) / Θ ^ 2 := by ring
  have e3 : ((0:ℝ) * Θ - 1 * 1) / Θ ^ 2 = -(1 / Θ ^ 2) := by ring
  rw [e2, e3]
  have t1 : 0 < d' * (((Θ - θ) / Θ) ^ 2 - 1 / Θ) := mul_pos hd'pos hB
  have t2 : 0 < (θ - 1) * ((2:ℕ) * ((Θ - θ) / Θ) ^ (2 - 1) * ((θ - d' * Θ) / Θ ^ 2) - -(1 / Θ ^ 2)) := by
    apply mul_pos (by linarith)
    have : 0 < (2:ℕ) * ((Θ - θ) / Θ) ^ (2 - 1) * ((θ - d' * Θ) / Θ ^ 2) := by positivity
    have : 0 < 1 / Θ ^ 2 := by positivity
    linarith
  linarith

theorem solution :
    (∀ Θ : ℝ, UtilityTokens.ICOChoice.thetaTilde < Θ →
      ∃ d : ℝ, HasDerivAt UtilityTokens.ICOChoice.Fden d Θ ∧ 0 < d) ∧
    StrictMonoOn UtilityTokens.ICOChoice.Fden (Set.Ioi UtilityTokens.ICOChoice.thetaTilde) := by
  refine ⟨ico_aux_deriv, ?_⟩
  apply strictMonoOn_of_deriv_pos (convex_Ioi _)
  · intro y hy
    obtain ⟨d, hd, _⟩ := ico_aux_deriv y hy
    exact hd.continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    obtain ⟨d, hd, hpos⟩ := ico_aux_deriv y hy
    rw [hd.deriv]; exact hpos
