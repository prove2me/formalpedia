-- Prove2me | solution 1 for SplitPMSGame.observation_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:21:47.605624+00:00
-- url     : https://prove2.me/submissions/a16dcdc6-adae-48d9-b488-74e1a27a0682

import Mathlib
import Definitions.Def_SplitPMSGame_IsCoreAlloc
import Definitions.Def_SplitPMSGame_ConstrainedTotallyBalanced

open SplitPMSGame in
theorem solution {Ñ N : Type*} [Fintype Ñ] [Fintype N] [DecidableEq N] (π : Ñ → N)
    (hπ : Function.Surjective π) (Gt : Finset Ñ → ℝ) (h : TotallyBalanced Gt) :
    ConstrainedTotallyBalanced π Gt ∧ TotallyBalanced (splitGame π Gt) := by
  have hmono : ∀ T S : Finset N, T ⊆ S → feasibleCoalition π T ⊆ feasibleCoalition π S := by
    intro T S hT a ha
    simp only [feasibleCoalition, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact hT ha
  constructor
  · intro S
    obtain ⟨y, hy⟩ := h (feasibleCoalition π S)
    unfold IsCoreAlloc at hy
    exact ⟨y, hy.1, fun T hT => hy.2 _ (hmono T S hT)⟩
  · intro S
    obtain ⟨y, hy⟩ := h (feasibleCoalition π S)
    unfold IsCoreAlloc at hy
    have hx : ∀ T : Finset N, ∑ i ∈ T, (∑ a ∈ Finset.univ.filter (fun a => π a = i), y a) =
        ∑ a ∈ feasibleCoalition π T, y a := by
      intro T
      rw [← Finset.sum_fiberwise_of_maps_to (s := feasibleCoalition π T) (t := T) (g := π)
        (fun a ha => by
          simp only [feasibleCoalition, Finset.mem_filter, Finset.mem_univ, true_and] at ha
          exact ha)]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      congr 1
      ext a
      simp only [feasibleCoalition, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ha
        exact ⟨by rw [ha]; exact hi, ha⟩
      · intro ha
        exact ha.2
    refine ⟨fun i => ∑ a ∈ Finset.univ.filter (fun a => π a = i), y a, ?_⟩
    unfold IsCoreAlloc splitGame
    refine ⟨?_, fun T hT => ?_⟩
    · rw [hx]
      exact hy.1
    · rw [hx]
      exact hy.2 _ (hmono T S hT)
