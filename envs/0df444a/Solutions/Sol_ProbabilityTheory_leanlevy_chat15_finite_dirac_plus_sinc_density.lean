-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat15_finite_dirac_plus_sinc_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:36:32.979083+00:00
-- url     : https://prove2.me/submissions/8fb36fdf-40d8-45fa-97a9-def1d5472d92

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- The Dirac and sinc-density pieces form a finite measure with finite coefficient. -/
theorem solution (a : ℝ≥0∞) (ha : a < ⊤) {ν : Measure ℝ}
    (h : ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν < ⊤) :
    IsFiniteMeasure (a • Measure.dirac (0 : ℝ) +
      ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))) := by
  refine ⟨?_⟩
  rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  refine ENNReal.add_lt_top.mpr ⟨?_, h⟩
  exact ENNReal.mul_lt_top ha (measure_lt_top _ _)
