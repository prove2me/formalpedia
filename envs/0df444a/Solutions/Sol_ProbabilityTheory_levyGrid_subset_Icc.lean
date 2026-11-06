-- Prove2me | solution 1 for ProbabilityTheory.levyGrid_subset_Icc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:57:07.994081+00:00
-- url     : https://prove2.me/submissions/02b70394-2c55-4062-89eb-c10b6de84f43

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution (T : ℕ) : levyGrid T ⊆ Set.Icc 0 (T : ℝ) :=
  Set.union_subset Set.inter_subset_right
    (Set.singleton_subset_iff.mpr ⟨Nat.cast_nonneg T, le_rfl⟩)
