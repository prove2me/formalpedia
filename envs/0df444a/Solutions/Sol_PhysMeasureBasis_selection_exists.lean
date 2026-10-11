-- Prove2me | solution 1 for PhysMeasureBasis.selection_exists
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:59:54.398559+00:00
-- url     : https://prove2.me/submissions/19c0cb62-40bc-416c-89d3-6d6c7095a394

-- Generated from PhysMeasureBasis.lean — solution of PhysMeasureBasis.selection_exists
import Mathlib
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysMeasureBasis



open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution :
    squareMeasure.fst ⊗ₘ squareMeasure.condKernel = squareMeasure := Measure.disintegrate _ _
