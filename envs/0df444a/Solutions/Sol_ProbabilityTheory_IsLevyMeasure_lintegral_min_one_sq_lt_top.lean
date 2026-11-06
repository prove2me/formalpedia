-- Prove2me | solution 1 for ProbabilityTheory.IsLevyMeasure.lintegral_min_one_sq_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:33:45.735397+00:00
-- url     : https://prove2.me/submissions/8d414013-2ed4-48da-9b11-1422bd7fc9f3

import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Mathlib.Data.ENNReal.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ENNReal Set ProbabilityTheory
open scoped NNReal ENNReal

theorem solution {ν : Measure ℝ} (hν : IsLevyMeasure ν) :
    ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ⊤ := by
  exact hν.2
