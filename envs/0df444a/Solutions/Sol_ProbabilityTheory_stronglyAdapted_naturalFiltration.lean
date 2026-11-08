-- Prove2me | solution 1 for ProbabilityTheory.stronglyAdapted_naturalFiltration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:55:09.708191+00:00
-- url     : https://prove2.me/submissions/fbe89a8a-c807-4b9e-ae7b-78f7bfb1e797

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

/-- A strongly measurable process is strongly adapted to its natural filtration. -/
theorem solution
    {X : ι → Ω → E} (hX : ∀ i, StronglyMeasurable (X i)) :
    StronglyAdapted
      (Filtration.natural (fun i => X i) hX) (fun i => X i) := by
  exact Filtration.stronglyAdapted_natural hX
