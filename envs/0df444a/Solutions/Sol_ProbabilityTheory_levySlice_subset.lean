-- Prove2me | solution 1 for ProbabilityTheory.levySlice_subset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:02:21.467896+00:00
-- url     : https://prove2.me/submissions/8479cd3c-d351-46c5-816b-369b0918f0cf

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution {ν : Measure ℝ} [SigmaFinite ν] (hν : IsLevyMeasure ν)
    (j : ℕ) : levySlice hν j ⊆ Set.Ioo (-1 : ℝ) 1 := by
  change (levyAnnulus (levyTruncationSeq hν (j + 1)) \
      levyAnnulus (levyTruncationSeq hν j)) ⊆ Set.Ioo (-1 : ℝ) 1
  exact Set.sdiff_subset.trans Set.inter_subset_left
