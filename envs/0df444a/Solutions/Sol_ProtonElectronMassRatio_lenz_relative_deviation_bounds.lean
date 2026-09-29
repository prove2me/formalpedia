-- Prove2me | solution 1 for ProtonElectronMassRatio.lenz_relative_deviation_bounds
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:20:45.467325+00:00
-- url     : https://prove2.me/submissions/ea97b108-475e-462b-b674-75922c3e1e44

import Mathlib
import Definitions.Def_ProtonElectronMassRatio_constants

open ProtonElectronMassRatio

theorem W2p_ProtonElectronMassRatio_lo :
    (3.14159265358979323846 : ℝ) ^ 5 < Real.pi ^ 5 :=
  pow_lt_pow_left₀ Real.pi_gt_d20 (by norm_num) (by norm_num)

theorem W2p_ProtonElectronMassRatio_hi :
    Real.pi ^ 5 < (3.14159265358979323847 : ℝ) ^ 5 :=
  pow_lt_pow_left₀ Real.pi_lt_d20 Real.pi_pos.le (by norm_num)

theorem W2p_ProtonElectronMassRatio_pi_pow_five_bounds :
    306.019684 < Real.pi ^ 5 ∧ Real.pi ^ 5 < 306.019685 := by
  have lo := W2p_ProtonElectronMassRatio_lo
  have hi := W2p_ProtonElectronMassRatio_hi
  constructor
  · have : (306.019684 : ℝ) < (3.14159265358979323846 : ℝ) ^ 5 := by norm_num
    linarith
  · have : (3.14159265358979323847 : ℝ) ^ 5 < 306.019685 := by norm_num
    linarith

theorem W2p_ProtonElectronMassRatio_lenz_expression_bounds :
    1836.1181 < lenzExpression ∧ lenzExpression < 1836.11811 := by
  have lo := W2p_ProtonElectronMassRatio_lo
  have hi := W2p_ProtonElectronMassRatio_hi
  unfold lenzExpression
  constructor
  · have : (1836.1181 : ℝ) < 6 * (3.14159265358979323846 : ℝ) ^ 5 := by norm_num
    linarith
  · have : 6 * (3.14159265358979323847 : ℝ) ^ 5 < 1836.11811 := by norm_num
    linarith

theorem W2p_ProtonElectronMassRatio_lenz_consistent_with_1951_measurement :
    |lenzExpression - lenz1951Measurement| < lenz1951Uncertainty := by
  have lo := W2p_ProtonElectronMassRatio_lo
  have hi := W2p_ProtonElectronMassRatio_hi
  unfold lenzExpression lenz1951Measurement lenz1951Uncertainty
  rw [abs_lt]
  constructor
  · have : -(0.05 : ℝ) < 6 * (3.14159265358979323846 : ℝ) ^ 5 - 1836.12 := by norm_num
    linarith
  · have : 6 * (3.14159265358979323847 : ℝ) ^ 5 - 1836.12 < 0.05 := by norm_num
    linarith

theorem W2p_ProtonElectronMassRatio_lenz_excluded_by_codata_2022 :
    codataUncertainty * 10 ^ 6 < |codataValue - lenzExpression| := by
  have hi := W2p_ProtonElectronMassRatio_hi
  unfold codataUncertainty codataValue lenzExpression
  apply lt_abs.mpr (Or.inl ?_)
  have : (0.000000032 : ℝ) * 10 ^ 6 < 1836.152673426 - 6 * (3.14159265358979323847 : ℝ) ^ 5 := by
    norm_num
  linarith

theorem W2p_ProtonElectronMassRatio_lenz_relative_deviation_bounds :
    0.0000188 < (codataValue - lenzExpression) / codataValue ∧
      (codataValue - lenzExpression) / codataValue < 0.0000189 := by
  have lo := W2p_ProtonElectronMassRatio_lo
  have hi := W2p_ProtonElectronMassRatio_hi
  unfold codataValue lenzExpression
  constructor
  · rw [lt_div_iff₀ (by norm_num)]
    have : (0.0000188 : ℝ) * 1836.152673426 <
        1836.152673426 - 6 * (3.14159265358979323847 : ℝ) ^ 5 := by norm_num
    linarith
  · rw [div_lt_iff₀ (by norm_num)]
    have : (1836.152673426 : ℝ) - 6 * (3.14159265358979323846 : ℝ) ^ 5 <
        0.0000189 * 1836.152673426 := by norm_num
    linarith

theorem W2p_ProtonElectronMassRatio_lenz_coincidence_not_exact (mproton melectron : ℝ)
    (h : mproton / melectron = codataValue) :
    mproton / melectron ≠ lenzExpression ∧
      codataUncertainty * 10 ^ 6 < |mproton / melectron - lenzExpression| ∧
      0.0000188 < (mproton / melectron - lenzExpression) / (mproton / melectron) ∧
      (mproton / melectron - lenzExpression) / (mproton / melectron) < 0.0000189 ∧
      |lenzExpression - lenz1951Measurement| < lenz1951Uncertainty := by
  rw [h]
  refine ⟨?_, W2p_ProtonElectronMassRatio_lenz_excluded_by_codata_2022,
    W2p_ProtonElectronMassRatio_lenz_relative_deviation_bounds.1,
    W2p_ProtonElectronMassRatio_lenz_relative_deviation_bounds.2,
    W2p_ProtonElectronMassRatio_lenz_consistent_with_1951_measurement⟩
  intro heq
  have hb := W2p_ProtonElectronMassRatio_lenz_expression_bounds.2
  have : (1836.11811 : ℝ) < codataValue := by unfold codataValue; norm_num
  linarith

theorem solution :
    0.0000188 < (codataValue - lenzExpression) / codataValue ∧
      (codataValue - lenzExpression) / codataValue < 0.0000189 := by
  apply W2p_ProtonElectronMassRatio_lenz_relative_deviation_bounds <;> assumption
