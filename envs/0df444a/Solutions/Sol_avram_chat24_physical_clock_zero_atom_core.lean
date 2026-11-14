-- Prove2me | solution 1 for avram_chat24_physical_clock_zero_atom_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:19.272193+00:00
-- url     : https://prove2.me/submissions/a15ab275-4f18-4960-bc92-2cefa1e245f9

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution (T : ℝ) :
    ((((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal) : Measure ℝ≥0) {0} = 0 := by
  have hm : Measurable Real.toNNReal := continuous_real_toNNReal.measurable
  rw [Measure.map_apply hm (measurableSet_singleton 0),
    Measure.restrict_apply ((measurableSet_singleton 0).preimage hm)]
  have hsub : Real.toNNReal ⁻¹' ({0} : Set ℝ≥0) ∩ Icc (0 : ℝ) T ⊆ {0} := by
    intro r hr
    have heq : Real.toNNReal r = 0 := hr.1
    have hcoe := congrArg (fun z : ℝ≥0 => (z : ℝ)) heq
    simpa only [Set.mem_singleton_iff, Real.toNNReal_of_nonneg hr.2.1,
      NNReal.coe_mk, NNReal.coe_zero] using hcoe
  exact measure_mono_null hsub
    (NullSingletonClass.measure_singleton (μ := (volume : Measure ℝ)) (0 : ℝ))
end
