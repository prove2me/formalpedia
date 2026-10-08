-- Prove2me | solution 1 for PalmQueueing.Formulas.fluid_set_identity
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:58:08.56228+00:00
-- url     : https://prove2.me/submissions/91cfcc08-a741-4810-9d04-b08dce6d291a

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Loynes_FluidQueue



namespace PalmQueueing.Formulas

open MeasureTheory
open PalmQueueing.Palm PalmQueueing.Loynes

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The supremum term of the fluid Loynes equation on `[u,t]` is bounded by `A_{u,t}`. -/
lemma fluid_sup_le_core (θ : Flow Ω) (A C : ℝ → ℝ → Ω → ℝ)
    (hA : IsFlowMeasure θ A) (hC : IsFlowMeasure θ C) (u t : ℝ) (hut : u ≤ t) (ω : Ω) :
    sSup {x | ∃ v : ℝ, u ≤ v ∧ v ≤ t ∧ x = A v t ω - C v t ω} ≤ A u t ω := by
  apply csSup_le
  · exact ⟨A t t ω - C t t ω, t, hut, le_rfl, rfl⟩
  · rintro x ⟨v, huv, hvt, rfl⟩
    have h1 : 0 ≤ C v t ω := hC.1 v t ω hvt
    have h2 : A u t ω = A u v ω + A v t ω := hA.2.1 u v t ω huv hvt
    have h3 : 0 ≤ A u v ω := hA.1 u v ω huv
    linarith

theorem fluid_set_identity_core (θ : Flow Ω) (A C : ℝ → ℝ → Ω → ℝ)
    (hA : IsFlowMeasure θ A) (hC : IsFlowMeasure θ C) (W : ℝ → Ω → ℝ)
    (hWcomp : IsCompatible θ W) (hW : IsFluidWorkload A C W) (s t : ℝ) (hst : s < t) (ω : Ω) :
    {u : ℝ | u ∈ Set.Icc s t ∧ C u t ω < W u ω}
      = {u : ℝ | u ∈ Set.Icc s t ∧ A u t ω < W t ω} := by
  ext u
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hu, hlt⟩
    refine ⟨hu, ?_⟩
    have hWt := hW u t ω hu.2
    have : W u ω + A u t ω - C u t ω ≤ W t ω := by rw [hWt]; exact le_max_left _ _
    linarith
  · rintro ⟨hu, hlt⟩
    refine ⟨hu, ?_⟩
    have hWt := hW u t ω hu.2
    have hsup := fluid_sup_le_core θ A C hA hC u t hu.2 ω
    rw [hWt] at hlt
    rcases max_cases (W u ω + A u t ω - C u t ω)
      (sSup {x | ∃ v : ℝ, u ≤ v ∧ v ≤ t ∧ x = A v t ω - C v t ω}) with h | h
    · rw [h.1] at hlt; linarith
    · rw [h.1] at hlt; linarith

end PalmQueueing.Formulas

open PalmQueueing.Formulas
open PalmQueueing.Palm PalmQueueing.Loynes
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (θ : Flow Ω) (A C : ℝ → ℝ → Ω → ℝ)
    (hA : IsFlowMeasure θ A) (hC : IsFlowMeasure θ C) (W : ℝ → Ω → ℝ)
    (hWcomp : IsCompatible θ W) (hW : IsFluidWorkload A C W) (s t : ℝ) (hst : s < t) (ω : Ω) :
    {u : ℝ | u ∈ Set.Icc s t ∧ C u t ω < W u ω}
      = {u : ℝ | u ∈ Set.Icc s t ∧ A u t ω < W t ω} := by
  exact fluid_set_identity_core θ A C hA hC W hWcomp hW s t hst ω
