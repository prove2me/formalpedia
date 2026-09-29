-- Prove2me | solution 1 for SocialEquilibrium.Existence.bestResponse_isContractible
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:19:52.69344+00:00
-- url     : https://prove2.me/submissions/8a42a1b3-ed32-424e-9714-14108992681c

import Mathlib
import Definitions.Def_SocialEquilibrium_Existence_IsContractible
import Definitions.Def_SocialEquilibrium_Existence_Game

namespace SocialEquilibrium.Existence

end SocialEquilibrium.Existence

open SocialEquilibrium.Existence

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (X : ∀ i, Set (E i)) (A : ∀ i : ι, Others X i → Set (X i))
    (f : ι → (∀ j, X j) → EReal)
    (hM : ∀ i (ā : Others X i), IsContractible (bestSet X A f i ā)) :
    ∀ a : ∀ j, X j, IsContractible (bestResponse X A f a) := by
  intro a
  choose z H h0 h1 using fun i => hM i (others X i a)
  refine ⟨⟨fun i => (z i).1, fun i => (z i).2⟩, ?_⟩
  refine ⟨⟨fun p => ⟨fun i => (H i (p.1, ⟨p.2.1 i, p.2.2 i⟩)).1,
    fun i => (H i (p.1, ⟨p.2.1 i, p.2.2 i⟩)).2⟩, ?_⟩, ?_, ?_⟩
  · apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    refine continuous_subtype_val.comp ((H i).continuous.comp ?_)
    refine Continuous.prodMk continuous_fst ?_
    exact Continuous.subtype_mk
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)) _
  · intro p
    apply Subtype.ext
    funext i
    simp [h0]
  · intro p
    apply Subtype.ext
    funext i
    simp [h1]
