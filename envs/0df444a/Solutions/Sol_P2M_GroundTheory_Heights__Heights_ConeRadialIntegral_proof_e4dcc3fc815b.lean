-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeRadialIntegral_proof_e4dcc3fc815b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:03:13.352131+00:00
-- url     : https://prove2.me/submissions/6ccc9d49-00cb-45df-a53a-e00cf0593c96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeRadialIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Set
open scoped ENNReal Pointwise
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ConeRadialIntegral
theorem _root_.solution : ConeRadialIntegral.Statement := by
  intro n m hm C hC hfin f hf
  set d : ℝ := ((2 * m : ℕ) : ℝ) with hd_def
  set c := Measure.hausdorffMeasure d {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ C} with hc_def
  have hd : 0 ≤ d := Nat.cast_nonneg _
  set D : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (2 * m * r ^ (2 * m - 1)) with hD_def
  have hDm : Measurable D := ENNReal.measurable_ofReal.comp (by fun_prop)
  set ν : Measure ℝ := Measure.map (fun y : EuclideanSpace ℂ (Fin n) => ‖y‖)
    ((Measure.hausdorffMeasure d).restrict C) with hν_def
  set ρ : Measure ℝ := c • (volume.restrict (Ioi (0 : ℝ))).withDensity D with hρ_def
  have h2m : 2 * m ≠ 0 := by omega

  have hνIio : ∀ r : ℝ, ν (Iio r) = ENNReal.ofReal (max r 0 ^ (2 * m)) * c := by
    intro r
    rw [hν_def, Measure.map_apply continuous_norm.measurable measurableSet_Iio,
      Measure.restrict_apply (measurableSet_Iio.preimage continuous_norm.measurable)]
    rcases le_or_gt r 0 with hr | hr
    · have hempty : (fun y : EuclideanSpace ℂ (Fin n) => ‖y‖) ⁻¹' Iio r ∩ C = ∅ := by
        ext y
        simp only [mem_inter_iff, mem_preimage, mem_Iio, mem_empty_iff_false, iff_false, not_and]
        intro h
        exact absurd (lt_of_lt_of_le h hr) (not_lt.2 (norm_nonneg y))
      rw [hempty, measure_empty, max_eq_right hr, zero_pow h2m, ENNReal.ofReal_zero, zero_mul]
    · have hset : (fun y : EuclideanSpace ℂ (Fin n) => ‖y‖) ⁻¹' Iio r ∩ C =
          r • {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ y ∈ C} := by
        ext y
        simp only [mem_inter_iff, mem_preimage, mem_Iio, mem_smul_set, mem_ofPred_eq]
        constructor
        · rintro ⟨hy, hyC⟩
          refine ⟨r⁻¹ • y, ⟨?_, hC y hyC r⁻¹ (inv_pos.2 hr)⟩, smul_inv_smul₀ hr.ne' y⟩
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, inv_mul_lt_iff₀ hr, mul_one]
          exact hy
        · rintro ⟨z, ⟨hz, hzC⟩, rfl⟩
          refine ⟨?_, hC z hzC r hr⟩
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
          calc r * ‖z‖ < r * 1 := mul_lt_mul_of_pos_left hz hr
            _ = r := mul_one r
      rw [hset, Measure.hausdorffMeasure_smul₀ hd hr.ne', max_eq_left hr.le, ENNReal.smul_def,
        smul_eq_mul]
      congr 1
      rw [hd_def, NNReal.rpow_natCast, ENNReal.ofReal_pow hr.le, ENNReal.coe_pow]
      congr 1
      rw [Real.nnnorm_of_nonneg hr.le, ENNReal.ofReal_eq_coe_nnreal hr.le]

  have hρIio : ∀ r : ℝ, ρ (Iio r) = ENNReal.ofReal (max r 0 ^ (2 * m)) * c := by
    intro r
    rw [hρ_def, Measure.smul_apply, smul_eq_mul, withDensity_apply _ measurableSet_Iio,
      Measure.restrict_restrict measurableSet_Iio, mul_comm]
    congr 1
    rcases le_or_gt r 0 with hr | hr
    · have hempty : Iio r ∩ Ioi (0 : ℝ) = ∅ := by
        ext t
        simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_empty_iff_false, iff_false, not_and]
        intro h1 h2
        linarith
      rw [hempty, Measure.restrict_empty, lintegral_zero_measure, max_eq_right hr, zero_pow h2m,
        ENNReal.ofReal_zero]
    · rw [max_eq_left hr.le, inter_comm, Ioi_inter_Iio]
      have hcont : Continuous (fun t : ℝ => 2 * (m : ℝ) * t ^ (2 * m - 1)) := by fun_prop
      rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self)]
      · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hr.le,
          intervalIntegral.integral_const_mul, integral_pow]
        congr 1
        obtain ⟨k, hk⟩ : ∃ k, 2 * m = k + 1 := ⟨2 * m - 1, by omega⟩
        have hk' : 2 * m - 1 = k := by omega
        have hkR : 2 * (m : ℝ) = (k : ℝ) + 1 := by exact_mod_cast hk
        rw [hk', hkR, hk, zero_pow (Nat.succ_ne_zero k), sub_zero]
        field_simp
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact mul_nonneg (by positivity) (pow_nonneg ht.1.le _)
  have hfinG : ∀ r : ℝ, ENNReal.ofReal (max r 0 ^ (2 * m)) * c ≠ ⊤ := fun r =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  have hνρ : ν = ρ := by
    refine Measure.ext_of_Ico' ν ρ (fun a b _ => ?_) (fun a b hab => ?_)
    · exact ne_top_of_le_ne_top (by rw [hνIio b]; exact hfinG b)
        (measure_mono Ico_subset_Iio_self)
    · have hsub : Iio a ⊆ Iio b := Iio_subset_Iio hab.le
      have hIco : Ico a b = Iio b \ Iio a := by
        ext t
        simp only [mem_Ico, mem_sdiff, mem_Iio, not_lt]
        tauto
      rw [hIco, measure_sdiff hsub measurableSet_Iio.nullMeasurableSet (by rw [hνIio a]; exact hfinG a),
        measure_sdiff hsub measurableSet_Iio.nullMeasurableSet (by rw [hρIio a]; exact hfinG a),
        hνIio, hνIio, hρIio, hρIio]
  calc ∫⁻ y in C, f ‖y‖ ∂(Measure.hausdorffMeasure d) = ∫⁻ r, f r ∂ν := by
        rw [hν_def, lintegral_map hf continuous_norm.measurable]
    _ = ∫⁻ r, f r ∂ρ := by rw [hνρ]
    _ = c * ∫⁻ r in Ioi 0, f r * D r := by
        rw [hρ_def, lintegral_smul_measure, smul_eq_mul,
          lintegral_withDensity_eq_lintegral_mul _ hDm hf]
        congr 1
        refine lintegral_congr fun r => ?_
        simp only [Pi.mul_apply]
        exact mul_comm _ _
end ConeRadialIntegral
end GroundTheory.Heights₂.Heights
