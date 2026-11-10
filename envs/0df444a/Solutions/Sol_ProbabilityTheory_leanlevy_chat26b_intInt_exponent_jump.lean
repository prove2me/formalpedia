-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat26b_intInt_exponent_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:01:09.172208+00:00
-- url     : https://prove2.me/submissions/97113aa4-6df3-4957-909d-edebd45d249c

import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_sigmaFinite
import Theorems.Thm_ProbabilityTheory_IsLevyMeasure_integrable_min_one_sq
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
import Theorems.Thm_ProbabilityTheory_leanlevy_chat26c_smear_integrand_narrow
import Theorems.Thm_ProbabilityTheory_leanlevy_chat26_norm_compensated_minimal
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
import Theorems.Thm_ProbabilityTheory_leanlevy_chat26_sinc_upper_minimal
import Mathlib.MeasureTheory.Function.SpecialFunctions.Sinc

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal Real

theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν) (ξ : ℝ) :
    ∫ u in (-1 : ℝ)..1, (∫ x, levyCompensatedIntegrand (ξ + u) x ∂ν)
      = 2 * ((∫ x, levyCompensatedIntegrand ξ x ∂ν)
          - ∫ x, Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ) ∂ν) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc (-1 : ℝ) 1)) := by
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    infer_instance
  haveI : SigmaFinite ν := hν.sigmaFinite
  have hmeas_joint : Measurable
      (fun p : ℝ × ℝ => levyCompensatedIntegrand (ξ + p.1) p.2) := by
    simp only [levyCompensatedIntegrand]
    refine (Measurable.sub (Measurable.sub ?_ measurable_const) ?_)
    · exact (((Complex.measurable_ofReal.comp measurable_snd).mul
        (Complex.measurable_ofReal.comp (measurable_const.add measurable_fst))).mul
        measurable_const).cexp
    · refine Measurable.mul ?_ ?_
      · exact ((Complex.measurable_ofReal.comp measurable_snd).mul
          (Complex.measurable_ofReal.comp (measurable_const.add measurable_fst))).mul
          measurable_const
      · exact measurable_const.ite
          ((isOpen_Iio.preimage (continuous_abs.comp continuous_snd)).measurableSet)
          measurable_const
  have h_int : Integrable (Function.uncurry (fun u x => levyCompensatedIntegrand (ξ + u) x))
      ((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod ν) := by
    apply Integrable.mono' (g := fun p : ℝ × ℝ =>
      (2 + 3 * (|ξ| + 1) ^ 2) * min 1 (p.2 ^ 2))
      ((hν.integrable_min_one_sq.const_mul (2 + 3 * (|ξ| + 1) ^ 2)).comp_snd _)
      hmeas_joint.aestronglyMeasurable
    have hfst : ∀ᵐ p ∂((volume.restrict (Set.uIoc (-1 : ℝ) 1)).prod ν),
        p.1 ∈ Set.uIoc (-1 : ℝ) 1 :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_uIoc)
    filter_upwards [hfst] with p hp
    have hp1 : |p.1| ≤ 1 := by
      rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hp
      rw [abs_le]
      exact ⟨hp.1.le, hp.2⟩
    calc ‖Function.uncurry (fun u x => levyCompensatedIntegrand (ξ + u) x) p‖
        = ‖levyCompensatedIntegrand (ξ + p.1) p.2‖ := rfl
      _ ≤ (2 + 3 * (ξ + p.1) ^ 2) * min 1 (p.2 ^ 2) :=
        leanlevy_chat26_norm_compensated_minimal _ _
      _ ≤ (2 + 3 * (|ξ| + 1) ^ 2) * min 1 (p.2 ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (le_min zero_le_one (sq_nonneg _))
          have hsq : (ξ + p.1) ^ 2 ≤ (|ξ| + 1) ^ 2 := by
            apply sq_le_sq'
            · nlinarith [abs_le.mp hp1, neg_abs_le ξ, le_abs_self ξ]
            · nlinarith [abs_le.mp hp1, neg_abs_le ξ, le_abs_self ξ]
          nlinarith [hsq]
  have hkernel_int : Integrable
      (fun x => Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ)) ν := by
    apply Integrable.mono' (g := fun x => 2 * min 1 (x ^ 2))
      (hν.integrable_min_one_sq.const_mul 2)
    · refine (Measurable.mul ?_ ?_).aestronglyMeasurable
      · exact (((Complex.measurable_ofReal.mul measurable_const).mul measurable_const).cexp)
      · exact Complex.measurable_ofReal.comp (measurable_const.sub Real.measurable_sinc)
    · refine ae_of_all _ fun x => ?_
      rw [norm_mul]
      have hnorm_exp : ‖Complex.exp (↑x * ↑ξ * Complex.I)‖ = 1 := by
        rw [show (↑x : ℂ) * ↑ξ * Complex.I = ↑(x * ξ) * Complex.I from by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      have hpos : 0 ≤ 1 - Real.sinc x := sub_nonneg.mpr (Real.sinc_le_one x)
      rw [hnorm_exp, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos]
      exact leanlevy_chat26_sinc_upper_minimal x
  have hpoint (x : ℝ) : (∫ u in (-1 : ℝ)..1, levyCompensatedIntegrand (ξ + u) x)
      = 2 * (levyCompensatedIntegrand ξ x
          - Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ)) := by
    have h := leanlevy_chat26c_smear_integrand_narrow ξ x
    linear_combination (-2 : ℂ) * h
  rw [intervalIntegral_integral_swap h_int]
  simp only [hpoint]
  rw [show (∫ y, 2 * (levyCompensatedIntegrand ξ y
        - Complex.exp (↑y * ↑ξ * Complex.I) * ((1 - Real.sinc y : ℝ) : ℂ)) ∂ν)
      = 2 * ∫ y, (levyCompensatedIntegrand ξ y
          - Complex.exp (↑y * ↑ξ * Complex.I) * ((1 - Real.sinc y : ℝ) : ℂ)) ∂ν
    from integral_const_mul _ _,
    integral_sub (integrable_levyCompensatedIntegrand hν ξ) hkernel_int]