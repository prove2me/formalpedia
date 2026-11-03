-- Prove2me | solution 1 for avram_chat07a_residual_limit_assembly
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:42:13.973712+00:00
-- url     : https://prove2.me/submissions/3edb4c52-2936-4c86-8981-91f7afaaece5

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
import Theorems.Thm_avram_chat07a_tendsto_approx
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
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (L x : ℝ)
    (hF : ∀ t : ℝ≥0, t ≤ (1 / 2 : ℝ≥0) →
      Integrable (fun ω =>
        w x - w (x - ((t : ℝ) * X.drift - X.X t ω))) P)
    (hPoly : ∀ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 →
      ∀ t : ℝ≥0,
        Integrable (fun ω => Polynomial.eval
          (Real.exp (-((t : ℝ) * X.drift - X.X t ω))) Q) P)
    (hSlope : ∀ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 →
      Tendsto (fun h : ℝ => h⁻¹ *
        (∫ ω, Polynomial.eval
          (Real.exp (-((Real.toNNReal h : ℝ) * X.drift -
            X.X (Real.toNNReal h) ω))) Q ∂P))
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (∫ y in Iio (0 : ℝ),
          Polynomial.eval (Real.exp y) Q ∂X.ν)))
    (hJoint : ∀ η : ℝ, 0 < η →
      ∃ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 ∧
        (∀ t : ℝ≥0, 0 < t → t ≤ (1 / 2 : ℝ≥0) →
          |(t : ℝ)⁻¹ * (∫ ω,
            (w x - w (x - ((t : ℝ) * X.drift - X.X t ω))) -
            Polynomial.eval (Real.exp (-((t : ℝ) * X.drift -
              X.X t ω))) Q ∂P)| ≤
            η * (2 * (∫ ω, (1 : ℝ) * X.drift -
              X.X 1 ω ∂P) + 2 * L)) ∧
        |(∫ y in Iio (0 : ℝ), Polynomial.eval (Real.exp y) Q ∂X.ν) -
          (∫ y in Iio (0 : ℝ), w x - w (x + y) ∂X.ν)| ≤
          η * ((∫ y in Iio (0 : ℝ), 1 - Real.exp y ∂X.ν) + 2)) :
    Tendsto
      (fun h : ℝ => h⁻¹ * (∫ ω,
        w x - w (x - ((Real.toNNReal h : ℝ) * X.drift -
          X.X (Real.toNNReal h) ω)) ∂P))
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (∫ y in Iio (0 : ℝ), w x - w (x + y) ∂X.ν)) := by
  let A : ℝ := 2 * (∫ ω, (1 : ℝ) * X.drift - X.X 1 ω ∂P) + 2 * L
  let B : ℝ := (∫ y in Iio (0 : ℝ), 1 - Real.exp y ∂X.ν) + 2
  let C : ℝ := |A| + |B| + 1
  have hC : 0 < C := by
    dsimp [C]
    have ha := abs_nonneg A
    have hb := abs_nonneg B
    linarith
  have hAC : A ≤ C := by
    dsimp [C]
    have ha := le_abs_self A
    have hb := abs_nonneg B
    linarith
  have hBC : B ≤ C := by
    dsimp [C]
    have ha := abs_nonneg A
    have hb := le_abs_self B
    linarith
  apply avram_chat07a_tendsto_approx
  intro ε hε
  let η : ℝ := ε / C
  have hη : 0 < η := div_pos hε hC
  obtain ⟨Q, hQ, hSource, hJump⟩ := hJoint η hη
  let g : ℝ → ℝ := fun h => h⁻¹ * (∫ ω,
    Polynomial.eval (Real.exp (-((Real.toNNReal h : ℝ) *
      X.drift - X.X (Real.toNNReal h) ω))) Q ∂P)
  let c : ℝ := ∫ y in Iio (0 : ℝ), Polynomial.eval (Real.exp y) Q ∂X.ν
  refine ⟨g, c, hSlope Q hQ, ?_, ?_⟩
  · calc
      |c - (∫ y in Iio (0 : ℝ), w x - w (x + y) ∂X.ν)| ≤
          η * B := hJump
      _ ≤ η * C := mul_le_mul_of_nonneg_left hBC hη.le
      _ = ε := by dsimp [η]; field_simp
  · have hpos : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0), 0 < h :=
      self_mem_nhdsWithin
    have hhalf : ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        h < (1 / 2 : ℝ) :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono
        (nhdsWithin_le_nhds)
    filter_upwards [hpos, hhalf] with h hhp hhb
    have htpos : 0 < Real.toNNReal h := by
      exact (Real.toNNReal_pos).mpr hhp
    have hthalf : Real.toNNReal h ≤ (1 / 2 : ℝ≥0) := by
      apply NNReal.coe_le_coe.mp
      simpa [Real.coe_toNNReal, max_eq_left (le_of_lt hhp)] using le_of_lt hhb
    have hsub := hSource (Real.toNNReal h) htpos hthalf
    have heq : (∫ ω,
        (w x - w (x - ((Real.toNNReal h : ℝ) * X.drift -
          X.X (Real.toNNReal h) ω))) -
        Polynomial.eval (Real.exp (-((Real.toNNReal h : ℝ) * X.drift -
          X.X (Real.toNNReal h) ω))) Q ∂P) =
       (∫ ω, w x - w (x - ((Real.toNNReal h : ℝ) * X.drift -
          X.X (Real.toNNReal h) ω)) ∂P) -
       (∫ ω, Polynomial.eval (Real.exp (-((Real.toNNReal h : ℝ) *
          X.drift - X.X (Real.toNNReal h) ω))) Q ∂P) :=
      integral_sub (hF _ hthalf) (hPoly Q hQ _)
    change |h⁻¹ * (∫ ω, w x - w (x - ((Real.toNNReal h : ℝ) *
      X.drift - X.X (Real.toNNReal h) ω)) ∂P) - g h| ≤ ε
    dsimp [g]
    have hcoe : (Real.toNNReal h : ℝ) = h := by
      simp [Real.coe_toNNReal, max_eq_left hhp.le]
    rw [hcoe] at heq hsub
    simp only [Real.coe_toNNReal, max_eq_left hhp.le] at ⊢
    rw [← mul_sub, ← heq]
    calc
      _ ≤ η * A := hsub
      _ ≤ η * C := mul_le_mul_of_nonneg_left hAC hη.le
      _ = ε := by dsimp [η]; field_simp
