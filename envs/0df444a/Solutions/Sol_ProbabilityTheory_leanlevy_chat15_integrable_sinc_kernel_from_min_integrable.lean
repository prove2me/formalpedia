-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat15_integrable_sinc_kernel_from_min_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:26:33.185191+00:00
-- url     : https://prove2.me/submissions/eb7575e7-a7b8-4c3c-b5a8-99ee934eeb69

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Sinc-damped Fourier integrability from the minimal square-integrability assumption. -/
theorem solution {ν : Measure ℝ}
    (hint : Integrable (fun x : ℝ => min 1 (x ^ 2)) ν) (ξ : ℝ)
    (hpos : ∀ x : ℝ, 0 ≤ 1 - Real.sinc x)
    (hbound : ∀ x : ℝ, 1 - Real.sinc x ≤ 2 * min 1 (x ^ 2)) :
    Integrable (fun x => Complex.exp (↑x * ↑ξ * Complex.I) *
      ((1 - Real.sinc x : ℝ) : ℂ)) ν := by
  apply Integrable.mono' (g := fun x => 2 * min 1 (x ^ 2))
    (hint.const_mul 2)
  · refine (Measurable.mul ?_ ?_).aestronglyMeasurable
    · exact (((Complex.measurable_ofReal.mul measurable_const).mul measurable_const).cexp)
    · exact Complex.measurable_ofReal.comp (measurable_const.sub Real.measurable_sinc)
  · refine ae_of_all _ fun x => ?_
    rw [norm_mul]
    have hnorm_exp : ‖Complex.exp (↑x * ↑ξ * Complex.I)‖ = 1 := by
      rw [show (↑x : ℂ) * ↑ξ * Complex.I = ↑(x * ξ) * Complex.I from by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [hnorm_exp, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hpos x)]
    exact hbound x
