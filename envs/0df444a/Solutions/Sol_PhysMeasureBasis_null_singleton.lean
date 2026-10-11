-- Prove2me | solution 1 for PhysMeasureBasis.null_singleton
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:59:52.113997+00:00
-- url     : https://prove2.me/submissions/c381cc1c-9337-4edc-a5c3-25fe20a005d5

-- Generated from PhysMeasureBasis.lean — solution of PhysMeasureBasis.null_singleton
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis



open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [MeasurableSingletonClass α] [NullSingletonClass μ] (a : α) : μ {a} = 0 := by

  convert MeasureTheory.NullSingletonClass.measure_singleton a;
  infer_instance
