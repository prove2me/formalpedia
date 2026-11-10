-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat26_charFun_smearedMeasure_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:43:16.440213+00:00
-- url     : https://prove2.me/submissions/bd30b3fc-5544-4085-961f-ad00861845eb

import Definitions.Def_LeanLevy_Levy_LevyKhintchineUniqueness
import Theorems.Thm_ProbabilityTheory_measurable_one_sub_sinc
import Theorems.Thm_ProbabilityTheory_leanlevy_chat26_lintegral_one_sub_sinc_public
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory ENNReal
open scoped NNReal ENNReal Real

variable {ν : Measure ℝ}

theorem solution (hν : IsLevyMeasure ν) (σ_sq : ℝ≥0) (ξ : ℝ) :
    charFun (smearedMeasure σ_sq ν) ξ
      = (((σ_sq : ℝ) / 6 : ℝ) : ℂ)
        + ∫ x, Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ) ∂ν := by
  haveI hAfin : IsFiniteMeasure (((σ_sq : ℝ≥0∞) / 6) • Measure.dirac (0 : ℝ)) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ 0), mul_one]
    exact ENNReal.div_lt_top (by simp) (by simp)
  haveI hBfin : IsFiniteMeasure (ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact leanlevy_chat26_lintegral_one_sub_sinc_public hν
  have hIntA : Integrable (fun x : ℝ => Complex.exp (↑ξ * ↑x * Complex.I))
      (((σ_sq : ℝ≥0∞) / 6) • Measure.dirac (0 : ℝ)) :=
    Integrable.of_bound (by fun_prop)
      1 (ae_of_all _ fun x => le_of_eq (by
        rw [show (↑ξ : ℂ) * ↑x * Complex.I = ↑(ξ * x) * Complex.I from by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _))
  have hIntB : Integrable (fun x : ℝ => Complex.exp (↑ξ * ↑x * Complex.I))
      (ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))) :=
    Integrable.of_bound (by fun_prop)
      1 (ae_of_all _ fun x => le_of_eq (by
        rw [show (↑ξ : ℂ) * ↑x * Complex.I = ↑(ξ * x) * Complex.I from by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _))
  rw [charFun_apply_real, smearedMeasure, integral_add_measure hIntA hIntB]
  congr 1
  · rw [integral_smul_measure, integral_dirac,
        show (↑ξ : ℂ) * ↑(0 : ℝ) * Complex.I = 0 from by simp, Complex.exp_zero]
    show ((↑σ_sq / 6 : ℝ≥0∞).toReal) • (1 : ℂ) = ↑((σ_sq : ℝ) / 6)
    rw [Complex.real_smul, mul_one]
    congr 1
    rw [ENNReal.toReal_div, ENNReal.coe_toReal, ENNReal.toReal_ofNat]
  · rw [integral_withDensity_eq_integral_toReal_smul measurable_one_sub_sinc
        (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have hsinc_nonneg : 0 ≤ 1 - Real.sinc x := sub_nonneg.mpr (Real.sinc_le_one x)
    simp only [ENNReal.toReal_ofReal hsinc_nonneg]
    show (1 - Real.sinc x : ℝ) • Complex.exp (↑ξ * ↑x * Complex.I)
      = Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ)
    rw [Complex.real_smul, show (↑ξ : ℂ) * ↑x * Complex.I = ↑x * ↑ξ * Complex.I from by ring]
    ring