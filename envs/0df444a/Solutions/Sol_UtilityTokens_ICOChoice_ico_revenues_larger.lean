-- Prove2me | solution 1 for UtilityTokens.ICOChoice.ico_revenues_larger
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:45:19.273308+00:00
-- url     : https://prove2.me/submissions/dea25715-84ee-46cb-ae4d-175fc684e210

import Mathlib
import Definitions.Def_UtilityTokens_ICOChoice_Setting
import Theorems.Thm_UtilityTokens_ICOChoice_proposition_1
import Theorems.Thm_UtilityTokens_ICOChoice_proposition_2
import Theorems.Thm_UtilityTokens_ICOChoice_lemma_1

open UtilityTokens.ICOChoice

theorem solution (Θ x f : ℝ) (hΘ : UtilityTokens.ICOChoice.thetaTilde < Θ) (hΘ3 : Θ ≤ 3)
    (hx : 0 < x) :
    UtilityTokens.ICOChoice.optPayoffT Θ x < UtilityTokens.ICOChoice.optPayoffI Θ x f + f ∧
    0 < UtilityTokens.ICOChoice.Fden Θ ∧
    UtilityTokens.ICOChoice.optPayoffI Θ x f - UtilityTokens.ICOChoice.optPayoffT Θ x =
      UtilityTokens.ICOChoice.Fden Θ * x - f := by
  obtain ⟨_, ⟨h1T, _⟩, _, hgt, _⟩ := lemma_1
  have hT1 : 1 < Θ := lt_trans h1T hΘ
  have hΘ0 : 0 < Θ := by linarith
  have hstar1 : 1 < thetaStar Θ := hgt Θ hΘ
  have hstarI : thetaStar Θ = thetaInterior Θ := by
    unfold thetaStar at hstar1 ⊢
    rcases le_total 1 (thetaInterior Θ) with h | h
    · exact max_eq_right h
    · rw [max_eq_left h] at hstar1; linarith
  -- the key inequality (Θ - θ*)^2 > Θ
  have hsq : Θ < (Θ - thetaStar Θ) ^ 2 := by
    rw [hstarI]
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
      push_neg at hc
      have : t ^ 2 ≤ ((1 + Real.sqrt 5) / 2) ^ 2 := by
        exact pow_le_pow_left₀ ht0.le hc 2
      nlinarith
    have hq : 0 < t ^ 2 - t - 1 := by nlinarith
    have hslt : 3 * t + 1 - t ^ 2 < s := by
      by_contra hc
      push_neg at hc
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
  have hbr : 0 < ((Θ - thetaStar Θ) / Θ) ^ 2 - 1 / Θ := by
    have : ((Θ - thetaStar Θ) / Θ) ^ 2 - 1 / Θ = ((Θ - thetaStar Θ) ^ 2 - Θ) / Θ ^ 2 := by
      field_simp
    rw [this]
    apply div_pos <;> nlinarith
  have hF : 0 < Fden Θ := by
    unfold Fden
    exact mul_pos (by linarith) hbr
  have hT := (proposition_1 Θ x hT1 hΘ3 hx).2.2.2
  have hI := (proposition_2 Θ x f hT1 hx).2.2.2.2.2
  have heq : optPayoffI Θ x f - optPayoffT Θ x = Fden Θ * x - f := by
    rw [hT, hI]
    unfold Fden
    field_simp
    ring
  refine ⟨?_, hF, heq⟩
  have := mul_pos hF hx
  linarith
