-- Prove2me | solution 1 for ProbabilityTheory.IsLevyMeasure.zero_singleton
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:34:12.034688+00:00
-- url     : https://prove2.me/submissions/c042d2ef-7794-4140-b178-b2082e02d7b2

import Definitions.Def_LeanLevy_Levy_LevyMeasure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ENNReal Set ProbabilityTheory
open scoped NNReal ENNReal

theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    ν {0} = 0 := by
  exact hν.1
