-- Prove2me | solution 1 for ProbabilityTheory.measurable_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:04:06.862046+00:00
-- url     : https://prove2.me/submissions/06c3b947-ffe3-44fb-a061-dd5b94cf8727

import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

universe u_1 u_2 u_3

theorem solution : ∀ {ι : Type u_1} {Ω : Type u_2} {E : Type u_3} [inst : MeasurableSpace Ω] [inst_1 : MeasurableSpace E] [inst_2 : Sub E]
  [@MeasurableSub₂ E inst_1 inst_2] {X : ι → Ω → E} {s t : ι},
  @Measurable Ω E inst inst_1 (X s) →
    @Measurable Ω E inst inst_1 (X t) → @Measurable Ω E inst inst_1 (@ProbabilityTheory.increment ι Ω E inst_2 X s t) := by
  intro ι Ω E _ _ _ _ X s t hs ht
  exact ht.sub hs
