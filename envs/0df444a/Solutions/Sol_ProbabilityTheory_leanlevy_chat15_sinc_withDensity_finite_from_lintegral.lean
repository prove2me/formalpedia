-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat15_sinc_withDensity_finite_from_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:36:41.702347+00:00
-- url     : https://prove2.me/submissions/e3c5727f-55c2-4696-9f23-d25150d1324f

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- The sinc-weighted measure is finite whenever its total density mass is finite. -/
theorem solution {ν : Measure ℝ}
    (h : ∫⁻ x, ENNReal.ofReal (1 - Real.sinc x) ∂ν < ⊤) :
    IsFiniteMeasure (ν.withDensity (fun x => ENNReal.ofReal (1 - Real.sinc x))) := by
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact h
