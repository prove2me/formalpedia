-- Prove2me | solution 1 for ProbabilityTheory.IsLimitOfIndicator.measurable
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:26:35.640042+00:00
-- url     : https://prove2.me/submissions/e71638a3-f40e-43b9-97ef-9adda09370e5

import Definitions.Def_BrownianMotion_Continuity_LimitModification_F000
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F001

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
#

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section aux

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : T → Ω → E} {c : ℝ≥0∞}
  {U : Set T}

section IndicatorProcess

variable {A : Set Ω} [hE : Nonempty E]

end IndicatorProcess

variable [PseudoEMetricSpace E] [hE : Nonempty E]
  [TopologicalSpace T] [SecondCountableTopology T]

theorem _root_.solution [MeasurableSpace E] [BorelSpace E] {Y X : T → Ω → E}
    (hX : ∀ t, Measurable (X t)) (hY : IsLimitOfIndicator Y X P U) (t : T) :
    Measurable (Y t) := by
  classical
  obtain ⟨A, hA, -, hlim, hext, hout⟩ := hY
  by_cases ht : t ∈ U
  · refine Measurable.of_edist_eq_zero (X := fun ω ↦ dense_denseCountable.extend
      (fun t' : denseCountable T ↦ indicatorProcess X A t' ω) t) ?_ (hext t ht)
    simp only [Dense.extend, IsDenseInducing.extend]
    refine measurable_limUnder_of_exists_tendsto (f := fun (t' : denseCountable T) ω ↦
      indicatorProcess X A t' ω) ?_ ?_
    · intro ω
      by_cases hω : ω ∈ A
      · obtain ⟨c, hc⟩ := hlim t ht ω hω
        exact ⟨c, by simpa [indicatorProcess_apply, hω] using hc⟩
      · exact ⟨hE.some, by simp only [indicatorProcess_apply, hω, if_false]; exact tendsto_const_nhds⟩
    · intro i
      exact measurable_indicatorProcess hA hX i
  · exact Measurable.of_edist_eq_zero (X := fun _ ↦ hE.some) measurable_const (hout t ht)

end ProbabilityTheory
