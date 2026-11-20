-- Prove2me | solution 1 for ProbabilityTheory.IsLimitOfIndicator.indicatorProcess
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:22:34.454314+00:00
-- url     : https://prove2.me/submissions/cdb24bba-158b-45e8-90b5-44a8c863548e

import Definitions.Def_BrownianMotion_Continuity_LimitModification_F003

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

theorem _root_.solution {Y X : T → Ω → E}
    (hY : IsLimitOfIndicator Y X P U) (A : Set Ω) (hA_meas : MeasurableSet A)
    (hA_ae : ∀ᵐ ω ∂P, ω ∈ A) :
    IsLimitOfIndicator (fun t ↦ indicatorProcess Y A t) X P U := by
  classical
  obtain ⟨B, hB, hBae, hlim, hext, hout⟩ := hY
  refine ⟨B ∩ A, hB.inter hA_meas, hBae.and hA_ae, ?_, ?_, ?_⟩
  · intro t ht ω hω
    exact hlim t ht ω hω.1
  · intro t ht ω
    by_cases hωA : ω ∈ A
    · have heq : (fun t' : denseCountable T ↦ ProbabilityTheory.indicatorProcess X (B ∩ A) t' ω)
          = fun t' : denseCountable T ↦ ProbabilityTheory.indicatorProcess X B t' ω := by
        funext t'
        simp [ProbabilityTheory.indicatorProcess_apply, hωA]
      rw [heq]
      simpa [ProbabilityTheory.indicatorProcess_apply, hωA] using hext t ht ω
    · have heq : (fun t' : denseCountable T ↦ ProbabilityTheory.indicatorProcess X (B ∩ A) t' ω)
          = fun _ : denseCountable T ↦ hE.some := by
        funext t'
        simp [ProbabilityTheory.indicatorProcess_apply, hωA]
      rw [heq]
      simp only [ProbabilityTheory.indicatorProcess_apply, hωA, if_false]
      have hne : (comap (Subtype.val : denseCountable T → T) (𝓝 t)).NeBot :=
        dense_denseCountable.comap_val_nhds_neBot t
      rw [edist_comm]
      exact edist_limUnder_const
  · intro t ht ω
    by_cases hωA : ω ∈ A
    · simpa [ProbabilityTheory.indicatorProcess_apply, hωA] using hout t ht ω
    · simp [ProbabilityTheory.indicatorProcess_apply, hωA]

end ProbabilityTheory
