-- Prove2me | solution 1 for PhysMeasureBasis.countable_null
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:59:53.274113+00:00
-- url     : https://prove2.me/submissions/3e70b5d3-e29f-4b8d-93e8-0c2baddfd6fd

-- Generated from PhysMeasureBasis.lean — solution of PhysMeasureBasis.countable_null
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis



open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : Measure α) [NullSingletonClass μ]
    {s : Set α} (hs : s.Countable) : μ s = 0 := by

  convert Set.Countable.measure_zero hs μ
