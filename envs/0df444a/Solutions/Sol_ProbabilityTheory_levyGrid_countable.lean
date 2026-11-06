-- Prove2me | solution 1 for ProbabilityTheory.levyGrid_countable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:56:19.772+00:00
-- url     : https://prove2.me/submissions/94b75baf-727e-4084-8e55-94d717aae475

import Definitions.Def_LeanLevy_RandomMeasure_LevyJumpPath
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.MeasureTheory.Measure.MeasureSpace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution (T : ℕ) : (levyGrid T).Countable :=
  ((Set.countable_range _).mono Set.inter_subset_left).union (Set.countable_singleton _)
