-- Prove2me | solution 1 for avram_chat07a_residual_and_poly_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:36:43.810524+00:00
-- url     : https://prove2.me/submissions/d612a9c2-b0ff-45df-9f7a-bd763bef979d

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
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
    (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) :
    (∀ t : ℝ≥0, t ≤ (1 / 2 : ℝ≥0) →
      Integrable (fun ω => w x -
        w (x - ((t : ℝ) * X.drift - X.X t ω))) P) ∧
    (∀ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 →
      ∀ t : ℝ≥0, Integrable
        (fun ω => Polynomial.eval
          (Real.exp (-((t : ℝ) * X.drift - X.X t ω))) Q) P) := by
  letI : IsProbabilityMeasure P := X.isProbability
  constructor
  · intro t ht
    have ht1 : t ≤ (1 : ℝ≥0) := le_trans ht (by norm_num)
    have hb :=
      avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
        X hX hBV w hw L hL hLip (x - (t : ℝ) * X.drift) t ht1
    have heq :
        (fun ω => w x - w (x - ((t : ℝ) * X.drift - X.X t ω))) =
        (fun ω => w x - w ((x - (t : ℝ) * X.drift) + X.X t ω)) := by
      funext ω
      congr 1
      ring
    rw [heq]
    exact (integrable_const _).sub hb
  · intro Q hQ t
    obtain ⟨p, hp, hPrim⟩ :=
      avram_wave5_04c_endpoint_zero_poly_as_exponential_primitive Q hQ
    have hi := avram_wave5_04c_actual_bv_poly_residual_primitive_integrable
      X hBV p hp t
    have heq :
      (fun ω => Polynomial.eval
        (Real.exp (-((t : ℝ) * X.drift - X.X t ω))) Q) =
      (fun ω => ∫ r in (0 : ℝ)..((t : ℝ) * X.drift -
        X.X t ω), Polynomial.eval (Real.exp (-r)) p) := by
      funext ω
      exact (hPrim ((t : ℝ) * X.drift - X.X t ω)).symm
    rw [heq]
    exact hi
