-- Prove2me | solution 1 for SocialEquilibrium.Existence.mem_bestResponse_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:14:24.596757+00:00
-- url     : https://prove2.me/submissions/4829dbea-83a5-46c5-b1ea-c6e97a7d0550

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

theorem aux_mbr_join_others {ι : Type*} [DecidableEq ι] {E : ι → Type*}
    (X : ∀ i, Set (E i)) (i : ι) (a : ∀ j, X j) :
    join X i (others X i a) (a i) = a := by
  unfold join others
  exact (Equiv.piSplitAt i (fun j => (X j : Type _))).symm_apply_apply a

end SocialEquilibrium.Existence

open SocialEquilibrium.Existence

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal) (a : ∀ j, X j) :
    a ∈ bestResponse X A f a ↔ IsEquilibrium X A f a := by
  constructor
  · intro h i
    obtain ⟨hA, hf⟩ := h i
    rw [aux_mbr_join_others] at hf
    refine ⟨hA, fun b hb => ?_⟩
    rw [hf]
    exact le_sSup ⟨b, hb, rfl⟩
  · intro h i
    obtain ⟨hA, hle⟩ := h i
    refine ⟨hA, ?_⟩
    rw [aux_mbr_join_others]
    apply le_antisymm
    · have : f i a = f i (join X i (others X i a) (a i)) := by rw [aux_mbr_join_others]
      rw [this]
      exact le_sSup ⟨a i, hA, rfl⟩
    · apply sSup_le
      rintro _ ⟨b, hb, rfl⟩
      exact hle b hb
