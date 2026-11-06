-- Prove2me | solution 1 for ProbabilityTheory.levyCompensatedIntegrand_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:20:21.859204+00:00
-- url     : https://prove2.me/submissions/1302c683-dcd6-4520-9fae-7547d52dca8a

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open ProbabilityTheory MeasureTheory Complex Set

theorem solution (x : ℝ) : levyCompensatedIntegrand 0 x = 0 := by
  simp [levyCompensatedIntegrand]
