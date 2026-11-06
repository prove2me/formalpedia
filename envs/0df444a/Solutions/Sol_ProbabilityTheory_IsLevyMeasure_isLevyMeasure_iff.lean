-- Prove2me | solution 1 for ProbabilityTheory.IsLevyMeasure.isLevyMeasure_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:08:19.281171+00:00
-- url     : https://prove2.me/submissions/704618a8-1549-4c29-a7ee-8a01dbf78a73

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The source definition characterises Lévy measures by two conjuncts. -/
theorem solution {ν : Measure ℝ} :
    IsLevyMeasure ν ↔ ν {0} = 0 ∧
      ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂ν < ⊤ := Iff.rfl
