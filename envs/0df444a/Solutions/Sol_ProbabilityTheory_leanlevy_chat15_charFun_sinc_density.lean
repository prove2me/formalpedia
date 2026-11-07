-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat15_charFun_sinc_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:46:37.344204+00:00
-- url     : https://prove2.me/submissions/39b1101d-afd8-49c9-a691-23174095f544

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Fourier characteristic function of a sinc-weighted density measure. -/
theorem solution (ξ : ℝ) {ν : Measure ℝ}
    (hfin : ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν < ⊤) :
    charFun (ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))) ξ
      = ∫ x, Complex.exp (↑x * ↑ξ * Complex.I) *
          ((1 - Real.sinc x : ℝ) : ℂ) ∂ν := by
  haveI : IsFiniteMeasure
      (ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hfin
  have hmeas : Measurable fun x : ℝ => ENNReal.ofReal (1 - Real.sinc x) :=
    ENNReal.measurable_ofReal.comp (measurable_const.sub Real.measurable_sinc)
  rw [charFun_apply_real,
    integral_withDensity_eq_integral_toReal_smul hmeas
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have hpos : 0 ≤ 1 - Real.sinc x := sub_nonneg.mpr (Real.sinc_le_one x)
  simp only [ENNReal.toReal_ofReal hpos]
  show (1 - Real.sinc x : ℝ) • Complex.exp (↑ξ * ↑x * Complex.I)
    = Complex.exp (↑x * ↑ξ * Complex.I) * ((1 - Real.sinc x : ℝ) : ℂ)
  rw [Complex.real_smul, show (↑ξ : ℂ) * ↑x * Complex.I =
    ↑x * ↑ξ * Complex.I from by ring]
  ring
