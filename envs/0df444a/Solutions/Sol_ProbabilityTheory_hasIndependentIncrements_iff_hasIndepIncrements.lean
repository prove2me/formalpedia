-- Prove2me | solution 1 for ProbabilityTheory.hasIndependentIncrements_iff_hasIndepIncrements
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T22:29:18.869106+00:00
-- url     : https://prove2.me/submissions/4582d71c-3264-446b-bcfa-ec4838ffad4c

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory MeasureTheory
theorem solution {ι : Type*} {Ω : Type*} {E : Type*} [Preorder ι]
    [MeasurableSpace Ω] [MeasurableSpace E] [Sub E]
    {X : ι → Ω → E} {μ : Measure Ω} :
    HasIndependentIncrements X μ ↔ HasIndepIncrements X μ := by
  exact Iff.rfl
