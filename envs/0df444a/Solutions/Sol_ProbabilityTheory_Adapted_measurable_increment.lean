-- Prove2me | solution 1 for ProbabilityTheory.Adapted.measurable_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T15:02:14.260276+00:00
-- url     : https://prove2.me/submissions/c544ef98-7318-4025-b4bc-a5bc5b9ef045

import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Process.Filtration
import Definitions.Def_LeanLevy_Processes_StochasticProcess

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory

universe u v w

variable {ι : Type u} {Ω : Type v} {E : Type w} {m : MeasurableSpace Ω}
variable [Preorder ι] [TopologicalSpace E] [MeasurableSpace E]
variable [BorelSpace E] [TopologicalSpace.MetrizableSpace E]
variable [Sub E] [MeasurableSub₂ E]

/-- Increments of an adapted process are measurable at their later time. -/
theorem solution {𝓕 : Filtration ι m} {X : ι → Ω → E}
    (hX : Adapted 𝓕 (fun i => X i))
    {s t : ι} (hst : s ≤ t) :
    Measurable[𝓕 t] (increment X s t) := by
  exact (hX t).sub ((hX s).mono (𝓕.mono hst) le_rfl)
