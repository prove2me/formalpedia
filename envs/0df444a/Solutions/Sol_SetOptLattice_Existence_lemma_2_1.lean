-- Prove2me | solution 1 for SetOptLattice.Existence.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:29:41.852596+00:00
-- url     : https://prove2.me/submissions/c5c86c08-49c9-4027-989b-815cd5074117

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

open Set Filter Topology
open scoped Pointwise

namespace Aux_SetOptLattice_lemma_2_1
open SetOptLattice.Existence

theorem sub_cl {Z : Type*} (Ψ : Set (Z → EReal)) (D : Set Z) : D ⊆ clPsi Ψ D := by
  intro z hz ψ _
  exact biInf_le ψ hz

theorem inf_cl {Z : Type*} (Ψ : Set (Z → EReal)) (D : Set Z) (ψ : Z → EReal) (hψ : ψ ∈ Ψ) :
    infExt ψ (clPsi Ψ D) = infExt ψ D := by
  apply le_antisymm
  · exact biInf_mono (sub_cl Ψ D)
  · exact le_iInf₂ (fun z hz => hz ψ hψ)

end Aux_SetOptLattice_lemma_2_1

open SetOptLattice.Existence Aux_SetOptLattice_lemma_2_1 in
theorem solution {Z : Type*} [Preorder Z] (Ψ : Set (Z → EReal))
    (hΨ : ∀ ψ ∈ Ψ, Monotone ψ) (D E : Set Z) :
    (SetLE Ψ D E ↔ clPsi Ψ E ⊆ clPsi Ψ D) ∧
      ((SetLE Ψ D E ∧ SetLE Ψ E D) ↔ clPsi Ψ D = clPsi Ψ E) ∧
      ∀ ψ ∈ Ψ, infExt ψ (clPsi Ψ D) = infExt ψ D := by
  have key : ∀ D E : Set Z, (SetLE Ψ D E ↔ clPsi Ψ E ⊆ clPsi Ψ D) := by
    intro D E
    constructor
    · intro h z hz ψ hψ
      exact le_trans (h ψ hψ) (hz ψ hψ)
    · intro h ψ hψ
      rw [← inf_cl Ψ D ψ hψ, ← inf_cl Ψ E ψ hψ]
      exact biInf_mono h
  refine ⟨key D E, ?_, fun ψ hψ => inf_cl Ψ D ψ hψ⟩
  rw [key D E, key E D]
  constructor
  · rintro ⟨h1, h2⟩
    exact Set.Subset.antisymm h2 h1
  · intro h
    exact ⟨h ▸ le_refl _, h ▸ le_refl _⟩
