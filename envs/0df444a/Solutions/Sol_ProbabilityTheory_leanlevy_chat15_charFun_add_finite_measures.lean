-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat15_charFun_add_finite_measures
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:53:04.518295+00:00
-- url     : https://prove2.me/submissions/bf6a6a7f-6453-4f84-93b3-8b26ef6b09d9

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Additivity of the Fourier characteristic functional on finite measures. -/
theorem solution {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ξ : ℝ) :
    charFun (μ + ν) ξ = charFun μ ξ + charFun ν ξ := by
  have hμ : Integrable (fun x : ℝ => Complex.exp (↑ξ * ↑x * Complex.I)) μ :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => le_of_eq (by
      rw [show (↑ξ : ℂ) * ↑x * Complex.I = ↑(ξ * x) * Complex.I from by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _))
  have hν : Integrable (fun x : ℝ => Complex.exp (↑ξ * ↑x * Complex.I)) ν :=
    Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => le_of_eq (by
      rw [show (↑ξ : ℂ) * ↑x * Complex.I = ↑(ξ * x) * Complex.I from by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _))
  simp only [charFun_apply_real]
  exact integral_add_measure hμ hν
