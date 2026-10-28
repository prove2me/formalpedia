-- Prove2me | solution 1 for SetOptLattice.Existence.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:47:56.601052+00:00
-- url     : https://prove2.me/submissions/de704a63-d5c7-4594-953d-7f8a83ea4f70

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

open Set Filter Topology
open scoped Pointwise

namespace Aux_SetOptLattice_lemma_2_4
open SetOptLattice.Existence

theorem sub_cl {Z : Type*} (Ψ : Set (Z → EReal)) (D : Set Z) : D ⊆ clPsi Ψ D := by
  intro z hz ψ _
  exact biInf_le ψ hz

theorem inf_cl {Z : Type*} (Ψ : Set (Z → EReal)) (D : Set Z) (ψ : Z → EReal) (hψ : ψ ∈ Ψ) :
    infExt ψ (clPsi Ψ D) = infExt ψ D := by
  apply le_antisymm
  · exact biInf_mono (sub_cl Ψ D)
  · exact le_iInf₂ (fun z hz => hz ψ hψ)

end Aux_SetOptLattice_lemma_2_4

open SetOptLattice.Existence Aux_SetOptLattice_lemma_2_4 in
theorem solution {Z : Type*} [Preorder Z] (Ψ : Set (Z → EReal))
    (hΨ : ∀ ψ ∈ Ψ, Monotone ψ) (𝒜 : Set (Set Z)) (h𝒜 : ∀ A ∈ 𝒜, IsPsiClosed Ψ A) :
    ∀ ψ ∈ Ψ, infExt ψ (latInf Ψ 𝒜) = ⨅ A ∈ 𝒜, infExt ψ A := by
  intro ψ hψ
  unfold latInf
  rw [inf_cl Ψ _ ψ hψ]
  unfold infExt
  apply le_antisymm
  · exact le_iInf₂ fun A hA => biInf_mono (subset_sUnion_of_mem hA)
  · refine le_iInf₂ fun z hz => ?_
    obtain ⟨A, hA, hzA⟩ := hz
    exact (biInf_le (fun A => ⨅ z ∈ A, ψ z) hA).trans (biInf_le ψ hzA)
