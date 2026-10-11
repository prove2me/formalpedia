-- Prove2me | solution 1 for PhysFunctionalAnalysis.l2_separable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T18:59:37.513992+00:00
-- url     : https://prove2.me/submissions/8d50ef8b-73df-4fe9-999b-c905d2ff6288

-- Generated from PhysFunctionalAnalysis.lean — solution of PhysFunctionalAnalysis.l2_separable
import Mathlib
import Definitions.Def_PhysFunctionalAnalysis
import Definitions.Def_PhysMeasureBasis
import Definitions.Def_ChapterA4
open PhysFunctionalAnalysis



open MeasureTheory Set
open scoped ENNReal lp

noncomputable section


open PhysMeasureBasis

set_option maxHeartbeats 1000000 in
theorem solution :
    TopologicalSpace.SeparableSpace (Lp ℝ 2 unitMeasure) := by

  exact inferInstanceAs (TopologicalSpace.SeparableSpace (MeasureTheory.Lp ℝ 2
    (MeasureTheory.Measure.restrict (MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Icc 0
    1))))
