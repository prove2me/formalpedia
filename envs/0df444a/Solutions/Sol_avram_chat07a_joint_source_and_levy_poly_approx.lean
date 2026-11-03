-- Prove2me | solution 1 for avram_chat07a_joint_source_and_levy_poly_approx
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:07:14.712561+00:00
-- url     : https://prove2.me/submissions/7515d0d7-73f4-49d7-b450-fbe66584ef86

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
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : X.BoundedVariation) (w : ℝ → ℝ) (hw : ContDiff ℝ 1 w) (L : ℝ) (hL : 0 ≤ L) (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|) (x : ℝ) (hgen : X.GeneratorIntegrable w x) (η : ℝ) (hη : 0 < η) : ∃ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 ∧ (∀ t : ℝ≥0, 0 < t → t ≤ (1 / 2 : ℝ≥0) → |(t : ℝ)⁻¹ * (∫ ω, (w x - w (x - ((t : ℝ) * X.drift - X.X t ω))) - Polynomial.eval (Real.exp (-((t : ℝ) * X.drift - X.X t ω))) Q ∂P)| ≤ η * (2 * (∫ ω, (1 : ℝ) * X.drift - X.X 1 ω ∂P) + 2 * L)) ∧ |(∫ y in Iio (0 : ℝ), Polynomial.eval (Real.exp y) Q ∂X.ν) - (∫ y in Iio (0 : ℝ), w x - w (x + y) ∂X.ν)| ≤ η * ((∫ y in Iio (0 : ℝ), 1 - Real.exp y ∂X.ν) + 2) := by
  let μ : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  let G : ℝ → ℝ := fun y => w x - w (x + y)
  let H : ℝ → ℝ := fun y => 1 - Real.exp y
  have hK : IntegrableOn (fun y => w (x + y) - w x) (Iio 0) X.ν :=
    boundedVariation_full_negative_jump_increment_integrable X hBV w x hgen
  have hG : Integrable G μ := by
    have heq : (fun y : ℝ => w x - w (x + y)) =
        (fun y => -(w (x + y) - w x)) := by
      funext y
      ring
    change Integrable (fun y => w x - w (x + y))
      (X.ν.restrict (Iio (0 : ℝ)))
    rw [heq]
    exact hK.neg
  have hAbs : IntegrableOn (fun y => |G y|) (Iio 0) X.ν := by
    change Integrable (fun y => |G y|) μ
    simpa only [Real.norm_eq_abs] using hG.norm
  have hMeas : Measurable (fun y : ℝ => |G y|) := by
    exact ((measurable_const.sub (hw.continuous.measurable.comp
      (measurable_const.add measurable_id))).abs)
  have htailν := avram_wave5_04c_integrable_signed_negative_jump_tail_DCT
    X.ν (fun y => |G y|) hMeas hAbs
  have htailν' : ∀ᶠ n : ℕ in atTop,
      (∫ y in Iio (0 : ℝ),
        if y < -(n : ℝ) then |G y| else 0 ∂X.ν) < η :=
    htailν.eventually (eventually_lt_nhds hη)
  have htailR :=
    avram_wave5_04c_actual_bv_residual_normalized_tail_uniform_vanish
      X hX hBV η hη
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (htailR.and htailν')
  have hNreal : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  obtain ⟨Q, hQ, hR, hJump⟩ :=
    avram_wave5_04c_actual_C1_joint_residual_levy_poly_choice
      w hw x (N : ℝ) η hNreal hη
  have hPoint (r : ℝ) (hr : 0 ≤ r) : |Polynomial.eval (Real.exp (-r)) Q - (w x - w (x - r))| ≤ η * (1 - Real.exp (-r)) + (if (N : ℝ) < r then 2 * L * r else 0) := by
    have hh := hR r hr
    have hLipR : |w x - w (x - r)| ≤ L * r := by
      have hk := hLip x (x - r)
      have hdif : |x - (x - r)| = r := by
        have heq : x - (x - r) = r := by ring
        rw [heq, abs_of_nonneg hr]
      simpa only [hdif] using hk
    by_cases hm : (N : ℝ) < r
    · simp only [if_pos hm] at hh ⊢
      nlinarith
    · simpa [hm] using hh
  have hSource (t : ℝ≥0) (htpos : 0 < t) (hthalf : t ≤ (1 / 2 : ℝ≥0)) : |(t : ℝ)⁻¹ * (∫ ω, (w x - w (x - ((t : ℝ) * X.drift - X.X t ω))) - Polynomial.eval (Real.exp (-((t : ℝ) * X.drift - X.X t ω))) Q ∂P)| ≤ η * (2 * (∫ ω, (1 : ℝ) * X.drift - X.X 1 ω ∂P) + 2 * L) := by
    have hbase :=
      avram_wave5_04c_actual_BV_original_residual_poly_error_normalized
        X hX hBV w hw L hL x (N : ℝ) η hη.le Q hPoint
        t (by exact le_trans hthalf (by norm_num))
    have hm :=
      avram_wave5_04c_actual_bv_residual_normalized_mean_le_two_terminal_mean
        X hX hBV t htpos hthalf
    have ht := (hN N le_rfl).1 t htpos hthalf
    have hi : 0 ≤ (t : ℝ)⁻¹ :=
      inv_nonneg.mpr (NNReal.coe_nonneg t)
    have hc : 0 ≤ 2 * L := by linarith
    calc
      |(t : ℝ)⁻¹ * (∫ ω, (w x - w (x - ((t : ℝ) * X.drift - X.X t ω))) - Polynomial.eval (Real.exp (-((t : ℝ) * X.drift - X.X t ω))) Q ∂P)| = (t : ℝ)⁻¹ * |∫ ω, (w x - w (x - ((t : ℝ) * X.drift - X.X t ω))) - Polynomial.eval (Real.exp (-((t : ℝ) * X.drift - X.X t ω))) Q ∂P| := by
          rw [abs_mul, abs_of_nonneg hi]
      _ ≤ (t : ℝ)⁻¹ * ( η * (∫ ω, (t : ℝ) * X.drift - X.X t ω ∂P) + 2 * L * (∫ ω, if (N : ℝ) < (t : ℝ) * X.drift - X.X t ω then (t : ℝ) * X.drift - X.X t ω else 0 ∂P)) :=
          mul_le_mul_of_nonneg_left hbase hi
      _ = η * ((t : ℝ)⁻¹ * (∫ ω, (t : ℝ) * X.drift - X.X t ω ∂P)) + 2 * L * ((t : ℝ)⁻¹ * (∫ ω, if (N : ℝ) < (t : ℝ) * X.drift - X.X t ω then (t : ℝ) * X.drift - X.X t ω else 0 ∂P)) := by ring
      _ ≤ η * (2 * (∫ ω, (1 : ℝ) * X.drift - X.X 1 ω ∂P)) + 2 * L * η :=
          add_le_add (mul_le_mul_of_nonneg_left hm hη.le)
            (mul_le_mul_of_nonneg_left (le_of_lt ht) hc)
      _ = η * (2 * (∫ ω, (1 : ℝ) * X.drift - X.X 1 ω ∂P) + 2 * L) := by ring
  have hF : Integrable (fun y => Polynomial.eval (Real.exp y) Q) μ := by
    exact avram_wave5_04c_actual_BV_endpoint_poly_levy_integrable X hBV Q hQ
  have hH : Integrable H μ := by
    have heq : (fun y : ℝ => 1 - Real.exp y) =
        (fun y => -(Real.exp (1 * y) - 1)) := by
      funext y
      simp only [one_mul]
      ring
    change Integrable (fun y => 1 - Real.exp y)
      (X.ν.restrict (Iio (0 : ℝ)))
    rw [heq]
    exact (bv_exponential_jump_integrable X hBV 1 (by norm_num)).neg
  let T : ℝ → ℝ := fun y =>
    if y < -(N : ℝ) then |G y| else 0
  have hT : Integrable T μ := by
    have hTi := hG.norm.indicator
      (measurableSet_Iio : MeasurableSet (Iio (-(N : ℝ))))
    have heq : T = (Iio (-(N : ℝ))).indicator (fun y => ‖G y‖) := by
      funext y
      simp only [T, Set.indicator, Set.mem_Iio, Real.norm_eq_abs]
    rw [heq]
    exact hTi
  have hμ : ∀ᵐ y ∂μ, y < 0 := by
    simpa only [μ, Set.mem_Iio] using
      (ae_restrict_mem (μ := X.ν) measurableSet_Iio)
  have hbd : ∀ᵐ y ∂μ, |Polynomial.eval (Real.exp y) Q - G y| ≤ η * H y + 2 * T y := by
    filter_upwards [hμ] with y hy
    have hh := hJump y hy
    by_cases htail : y < -(N : ℝ)
    · simpa only [G, H, T, if_pos htail] using hh
    · simpa [G, H, T, htail] using hh
  have hνbase :=
    avram_wave5_04c_signed_payoff_BV_Levy_L1_error_transfer
      μ (fun y => Polynomial.eval (Real.exp y) Q) G H T
      hF hG hH hT η hη.le hbd
  have hνtail : (∫ y, T y ∂μ) < η := (hN N le_rfl).2
  have hν : |(∫ y in Iio (0 : ℝ), Polynomial.eval (Real.exp y) Q ∂X.ν) - (∫ y in Iio (0 : ℝ), w x - w (x + y) ∂X.ν)| ≤ η * ((∫ y in Iio (0 : ℝ), 1 - Real.exp y ∂X.ν) + 2) := by
    change |(∫ y, Polynomial.eval (Real.exp y) Q ∂μ) -
      (∫ y, G y ∂μ)| ≤ η * ((∫ y, H y ∂μ) + 2)
    calc
      _ ≤ η * (∫ y, H y ∂μ) + 2 * (∫ y, T y ∂μ) := hνbase
      _ ≤ η * ((∫ y, H y ∂μ) + 2) := by
        nlinarith [hνtail, hη.le]
  exact ⟨Q, hQ, hSource, hν⟩
