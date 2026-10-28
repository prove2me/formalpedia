-- Prove2me | solution 1 for SetOptLattice.Existence.proposition_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:12:42.468476+00:00
-- url     : https://prove2.me/submissions/9a0c4205-0213-44d2-a38b-2e850e9c44e0

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

open Set Filter Topology
open scoped Pointwise

namespace SetOptLatticeAux22
open SetOptLattice.Existence

theorem sub_cl {Z : Type*} (Ψ : Set (Z → EReal)) (D : Set Z) : D ⊆ clPsi Ψ D := by
  intro z hz ψ _
  exact biInf_le ψ hz

theorem inf_cl {Z : Type*} (Ψ : Set (Z → EReal)) (D : Set Z) (ψ : Z → EReal) (hψ : ψ ∈ Ψ) :
    infExt ψ (clPsi Ψ D) = infExt ψ D := by
  apply le_antisymm
  · exact biInf_mono (sub_cl Ψ D)
  · exact le_iInf₂ fun z hz => hz ψ hψ

end SetOptLatticeAux22

open SetOptLattice.Existence SetOptLatticeAux22 in
theorem solution {Z : Type*} [Preorder Z] (Ψ : Set (Z → EReal))
    (hΨ : ∀ ψ ∈ Ψ, Monotone ψ) :
    (∀ D : Set Z, D ⊆ clPsi Ψ D) ∧
      (∀ D E : Set Z, D ⊆ E → clPsi Ψ D ⊆ clPsi Ψ E) ∧
      ∀ D : Set Z, clPsi Ψ D = clPsi Ψ (clPsi Ψ D) := by
  refine ⟨fun D => sub_cl Ψ D, ?_, ?_⟩
  · intro D E hDE z hz ψ hψ
    exact le_trans (biInf_mono hDE) (hz ψ hψ)
  · intro D
    ext z
    constructor
    · intro h
      change ∀ ψ ∈ Ψ, infExt ψ (clPsi Ψ D) ≤ ψ z
      intro ψ hψ
      rw [inf_cl Ψ D ψ hψ]
      exact h ψ hψ
    · intro h
      change ∀ ψ ∈ Ψ, infExt ψ D ≤ ψ z
      intro ψ hψ
      rw [← inf_cl Ψ D ψ hψ]
      exact h ψ hψ
