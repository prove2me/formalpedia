-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat15_charFun_explicit_sinc_smear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:42:26.247374+00:00
-- url     : https://prove2.me/submissions/b26127e8-431f-4fe9-b8c8-7ca29a47f5c3

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Fourier transform of the explicit atom-plus-sinc-density measure. -/
theorem solution (σ_sq : ℝ≥0) (ξ : ℝ) {ν : Measure ℝ}
    (hfin : ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν < ⊤) :
    charFun ((((σ_sq : ℝ≥0∞) / 6) • Measure.dirac (0 : ℝ)) +
      ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))) ξ
      = (((σ_sq : ℝ) / 6 : ℝ) : ℂ) +
        ∫ x, Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ) ∂ν := by
  haveI hAfin : IsFiniteMeasure (((σ_sq : ℝ≥0∞) / 6) • Measure.dirac (0 : ℝ)) := by
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (Set.mem_univ 0), mul_one]
    exact ENNReal.div_lt_top (by simp) (by simp)
  haveI hBfin : IsFiniteMeasure
      (ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hfin
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
  rw [charFun_apply_real, integral_add_measure hIntA hIntB]
  congr 1
  · rw [integral_smul_measure, integral_dirac,
        show (↑ξ : ℂ) * ↑(0 : ℝ) * Complex.I = 0 from by simp, Complex.exp_zero]
    show ((↑σ_sq / 6 : ℝ≥0∞).toReal) • (1 : ℂ) = ↑((σ_sq : ℝ) / 6)
    rw [Complex.real_smul, mul_one]
    congr 1
    rw [ENNReal.toReal_div, ENNReal.coe_toReal, ENNReal.toReal_ofNat]
  · have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (1 - Real.sinc x) :=
      ENNReal.measurable_ofReal.comp (measurable_const.sub Real.measurable_sinc)
    rw [integral_withDensity_eq_integral_toReal_smul hmeas
        (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    have hpos : 0 ≤ 1 - Real.sinc x := sub_nonneg.mpr (Real.sinc_le_one x)
    simp only [ENNReal.toReal_ofReal hpos]
    show (1 - Real.sinc x : ℝ) • Complex.exp (↑ξ * ↑x * Complex.I)
      = Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ)
    rw [Complex.real_smul, show (↑ξ : ℂ) * ↑x * Complex.I =
      ↑x * ↑ξ * Complex.I from by ring]
    ring
