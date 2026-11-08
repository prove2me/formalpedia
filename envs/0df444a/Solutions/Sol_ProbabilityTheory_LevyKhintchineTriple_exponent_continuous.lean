-- Prove2me | solution 1 for ProbabilityTheory.LevyKhintchineTriple.exponent_continuous
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:56:49.220898+00:00
-- url     : https://prove2.me/submissions/7b8e87cc-d9a7-4843-b16e-bbcbd575e04f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_continuous_integral_levyCompensatedIntegrand
import Mathlib.Topology.Defs.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (T : LevyKhintchineTriple) :
    Continuous T.exponent := by
  unfold LevyKhintchineTriple.exponent
  have hInt := continuous_integral_levyCompensatedIntegrand T.levyMeasure_isLevyMeasure
  fun_prop
