-- Prove2me | solution 1 for avram_chat07a_final_drift_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:36:47.995118+00:00
-- url     : https://prove2.me/submissions/fb994b2a-4cc9-440c-99f4-116270de4868

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_endpoint_zero_poly_as_exponential_primitive
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_right_slope
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_levy_integral
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_integrable_signed_negative_jump_tail_DCT
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_tail_uniform_vanish
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_joint_residual_levy_poly_choice
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_BV_original_residual_poly_error_normalized
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_normalized_mean_le_two_terminal_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_BV_endpoint_poly_levy_integrable
import Theorems.Thm_AvramDividend_Classical_bv_exponential_jump_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_signed_payoff_BV_Levy_L1_error_transfer
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_poly_residual_primitive_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_original_C1_source_drift_expectation_right_slope
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) (hgen : X.GeneratorIntegrable w x)
    (hRes : Tendsto
      (fun h : ℝ => h⁻¹ * (∫ ω,
        w x - w (x - ((Real.toNNReal h : ℝ) * X.drift -
          X.X (Real.toNNReal h) ω)) ∂P))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y in Iio (0 : ℝ), w x - w (x + y) ∂X.ν))) :
    Tendsto (fun h : ℝ =>
      h⁻¹ * ((∫ ω, w (x + X.X (Real.toNNReal h) ω) ∂P) - w x))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (X.generator w x)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hD :=
    avram_wave5_04c_original_C1_source_drift_expectation_right_slope
      X w hwC1 L hL hLip x X.drift
  have hJ :
      (∫ y in Iio (0 : ℝ), w x - w (x + y) ∂X.ν) =
      -(∫ y in Iio (0 : ℝ), w (x + y) - w x ∂X.ν) := by
    calc
      _ = ∫ y in Iio (0 : ℝ), -(w (x + y) - w x) ∂X.ν := by
        apply integral_congr_ae
        filter_upwards [] with y
        ring
      _ = _ := integral_neg _
  have hlimit := hD.sub hRes
  have hgenEq :=
    boundedVariation_generator_physical_drift_representation X hBV w x hgen
  rw [hJ, sub_neg_eq_add] at hlimit
  rw [hgenEq]
  apply hlimit.congr'
  have hpos : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), 0 < h :=
    self_mem_nhdsWithin
  have hsmall : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), h < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, hsmall] with h hhp hh1
  have ht : Real.toNNReal h ≤ (1 : ℝ≥0) := by
    apply NNReal.coe_le_coe.mp
    simpa [Real.coe_toNNReal, max_eq_left hhp.le] using le_of_lt hh1
  let t : ℝ≥0 := Real.toNNReal h
  let d : ℝ := X.drift
  have ha : Integrable (fun ω => w (x + X.X t ω)) P :=
    avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
      X hX hBV w hwC1 L hL hLip x t ht
  have hb₀ : Integrable (fun ω => w ((x - (t : ℝ) * d) + X.X t ω)) P :=
    avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
      X hX hBV w hwC1 L hL hLip (x - (t : ℝ) * d) t ht
  have hb : Integrable (fun ω => w (x + X.X t ω - d * h)) P := by
    have hcoe : (t : ℝ) = h := by
      dsimp [t]
      simp [Real.coe_toNNReal, max_eq_left hhp.le]
    convert hb₀ using 1
    funext ω
    congr 1
    dsimp [d]
    rw [hcoe]
    ring
  have hsplit :
      ((∫ ω, w (x + X.X t ω) ∂P) - w x) =
       (∫ ω, w (x + X.X t ω) - w (x + X.X t ω - d * h) ∂P) +
       ((∫ ω, w (x + X.X t ω - d * h) ∂P) - w x) := by
    rw [integral_sub ha hb]
    ring
  have hshift :
      ((∫ ω, w (x + X.X t ω - d * h) ∂P) - w x) =
        -(∫ ω, w x - w (x + X.X t ω - d * h) ∂P) := by
    have hc : (∫ ω : Ω, w x ∂P) = w x := by simp
    rw [integral_sub (integrable_const _) hb]
    rw [hc]
    ring
  have hcoe : (t : ℝ) = h := by
      dsimp [t]
      simp [Real.coe_toNNReal, max_eq_left hhp.le]
  have heq : ∀ ω : Ω, (x + X.X t ω - d * h) =
        (x - ((t : ℝ) * X.drift - X.X t ω)) := by
    intro ω
    dsimp [d]
    rw [hcoe]
    ring
  change
    (∫ ω, h⁻¹ * (w (x + X.X t ω) -
      w (x + X.X t ω - d * h)) ∂P) -
      h⁻¹ * (∫ ω, w x - w (x - ((t : ℝ) * X.drift -
        X.X t ω)) ∂P) =
      h⁻¹ * ((∫ ω, w (x + X.X t ω) ∂P) - w x)
  rw [integral_const_mul]
  have hresEq : (∫ ω, w x - w (x - ((t : ℝ) * X.drift -
        X.X t ω)) ∂P) =
      (∫ ω, w x - w (x + X.X t ω - d * h) ∂P) := by
    apply integral_congr_ae
    filter_upwards [] with ω
    rw [← heq ω]
  rw [hresEq, hsplit, hshift]
  ring
