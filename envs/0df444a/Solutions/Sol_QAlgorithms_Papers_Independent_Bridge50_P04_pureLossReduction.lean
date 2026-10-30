-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Bridge50.P04.pureLossReduction
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T12:59:04.705309+00:00
-- url     : https://prove2.me/submissions/b862f8cd-f0a0-4972-9f5d-af12bd948988

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P04

open QAlgorithms.Papers.Independent.Bridge50.P04

open QAlgorithms.Papers.Independent.Information100.P63 (logTwo)

open QAlgorithms.Papers.Independent.Frontier30.P24 (bosonicEntropy)

theorem solution (tau : ℝ) (hTauPos : 0 < tau) (hTauLt : tau < 1) :
    analyticRate tau 0 = pureLossRate tau := by
  have h1 : 1 - tau ≠ 0 := by linarith
  have h2 : 1 + tau ≠ 0 := by linarith
  have h3 : tau ≠ 0 := hTauPos.ne'
  have h4 : 1 - tau ^ 2 ≠ 0 := by nlinarith
  have hA : ((2 * (1 + tau) / tau + 0) / (1 + tau) - 1 - 1) / 2 = ((2 - tau) / tau - 1) / 2 := by
    field_simp
    ring
  have hB : ((tau * (2 * (1 + tau) / tau + 0) - (1 + tau) ^ 2) / (1 - tau ^ 2) - 1) / 2 = 0 := by
    have : tau * (2 * (1 + tau) / tau + 0) - (1 + tau) ^ 2 = 1 - tau ^ 2 := by
      field_simp
      ring
    rw [this, div_self h4]
    norm_num
  have hC : 2 * (1 + tau) / (Real.exp 1 * (1 - tau) * (2 * (1 + tau) / tau + 0)) =
      tau / ((1 - tau) * Real.exp 1) := by
    have := Real.exp_pos 1
    field_simp
    ring
  have hE : bosonicEntropy 0 = 0 := by norm_num [bosonicEntropy]
  unfold analyticRate pureLossRate equivalentNoise lossNoise
  simp only
  rw [hA, hB, hC, hE, sub_zero]
