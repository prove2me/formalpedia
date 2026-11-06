-- Prove2me | solution 1 for ProbabilityTheory.levyCompensatedIntegrand_def
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T09:22:34.959557+00:00
-- url     : https://prove2.me/submissions/fd209704-221a-4bf4-b045-a51906269c24

import Definitions.Def_LeanLevy_Levy_CompensatedIntegral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Complex ENNReal Set ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate

theorem solution (ξ x : ℝ) :
    levyCompensatedIntegrand ξ x =
      exp (↑x * ↑ξ * I) - 1 - ↑x * ↑ξ * I * if |x| < 1 then 1 else 0 :=
  rfl
