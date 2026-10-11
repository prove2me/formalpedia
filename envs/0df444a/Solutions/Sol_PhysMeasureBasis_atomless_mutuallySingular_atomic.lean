-- Prove2me | solution 1 for PhysMeasureBasis.atomless_mutuallySingular_atomic
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:59:58.914048+00:00
-- url     : https://prove2.me/submissions/9eefb0a2-632d-4c8a-a0f5-0808b3be3b77

-- Generated from PhysMeasureBasis.lean — solution of PhysMeasureBasis.atomless_mutuallySingular_atomic
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis



open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ ν : Measure α) [NullSingletonClass μ]
    {A : Set α} (hA : A.Countable) (hν : ν Aᶜ = 0) :
    μ ⟂ₘ ν := by

  refine ⟨A, ?_, ?_⟩
  · exact hA.measurableSet;
  · exact ⟨ hA.measure_zero μ, hν ⟩
