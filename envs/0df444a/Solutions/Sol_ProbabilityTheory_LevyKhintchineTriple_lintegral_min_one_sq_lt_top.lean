-- Prove2me | solution 1 for ProbabilityTheory.LevyKhintchineTriple.lintegral_min_one_sq_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:39:14.694277+00:00
-- url     : https://prove2.me/submissions/2a73c5b9-9ecd-4381-b9e7-9659c4498d5c

import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Mathlib.Data.ENNReal.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ENNReal Set ProbabilityTheory
open scoped NNReal ENNReal

theorem solution (T : LevyKhintchineTriple) :
    ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂T.levyMeasure < ⊤ := by
  exact T.levyMeasure_isLevyMeasure.2
