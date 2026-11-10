-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P89.loss_protection_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T03:33:27.475742+00:00
-- url     : https://prove2.me/submissions/f7eb4e1b-8114-493a-8149-bcea8b58cbc2

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P89

open scoped BigOperators ComplexConjugate

noncomputable section

open QAlgorithms.Papers.Independent.Intakenext100.P89 in
theorem solution (d : Devices) (hLoss : 0 < d.beta * d.tauS) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∀ (n : ℕ), 0 < n → ∀ (L : ℝ), 0 ≤ L →
      travelingSurvival d k n L < (1 : ℝ) / 2 ∧
      stationarySurvival d k n L < (1 : ℝ) / 2 := by
  have hc1 : chipSurvival d < 1 := by
    unfold chipSurvival
    rw [Real.exp_lt_one_iff]
    have := mul_pos hLoss d.cChip_pos
    linarith
  have hc0 : 0 ≤ chipSurvival d := (Real.exp_pos _).le
  have he0 : 0 < etaSD d := mul_pos d.etaS_pos d.etaD_pos
  have he1 : etaSD d ≤ 1 := mul_le_one₀ d.etaS_le d.etaD_pos.le d.etaD_le
  have hg0 : 0 ≤ etaGHZ d := by
    unfold etaGHZ; exact div_nonneg he0.le (by linarith)
  have hg1 : etaGHZ d ≤ 1 := by
    unfold etaGHZ; rw [div_le_one (by linarith)]; linarith
  have hF0 : 0 ≤ fiberSurvival d := (Real.exp_pos _).le
  have hF1 : fiberSurvival d ≤ 1 := by
    unfold fiberSurvival
    rw [Real.exp_le_one_iff]
    have := mul_nonneg (mul_nonneg d.alpha_pos.le d.tauF_nonneg) d.cFiber_pos.le
    linarith
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (by norm_num : (0:ℝ) < 1 / 2) hc1
  refine ⟨K, fun k hk n hn L hL => ?_⟩
  have hpow : chipSurvival d ^ (k + 2) ≤ chipSurvival d ^ K :=
    pow_le_pow_of_le_one hc0 hc1.le (by omega)
  have hp0 : 0 ≤ chipSurvival d ^ (k + 2) := pow_nonneg hc0 _
  have hTF0 : 0 ≤ travelingFactor d k := by
    unfold travelingFactor
    exact mul_nonneg (mul_nonneg hp0 hg0) d.etaC_pos.le
  have hTF : travelingFactor d k ≤ chipSurvival d ^ (k + 2) := by
    unfold travelingFactor
    rw [mul_assoc]
    exact mul_le_of_le_one_right hp0 (mul_le_one₀ hg1 d.etaC_pos.le d.etaC_le)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hE1 : Real.exp (-d.alpha * L / (2 * (n : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have := mul_nonneg d.alpha_pos.le hL
    linarith
  have hE2 : Real.exp (-d.alpha * L / (n : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg _ hn'.le
    have := mul_nonneg d.alpha_pos.le hL
    linarith
  have hSF0 : 0 ≤ stationaryFactor d k := by
    unfold stationaryFactor; exact mul_nonneg hTF0 hF0
  have hSF : stationaryFactor d k ≤ travelingFactor d k := by
    unfold stationaryFactor; exact mul_le_of_le_one_right hTF0 hF1
  constructor
  · unfold travelingSurvival
    calc Real.exp (-d.alpha * L / (2 * (n : ℝ))) * travelingFactor d k ≤ travelingFactor d k :=
          mul_le_of_le_one_left hTF0 hE1
      _ < 1 / 2 := by linarith
  · unfold stationarySurvival
    calc Real.exp (-d.alpha * L / (n : ℝ)) * stationaryFactor d k ≤ stationaryFactor d k :=
          mul_le_of_le_one_left hSF0 hE2
      _ < 1 / 2 := by linarith
