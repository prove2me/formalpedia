-- Prove2me | solution 1 for SetOptLattice.Existence.proposition_2_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T10:57:39.399306+00:00
-- url     : https://prove2.me/submissions/933c1af6-368d-4635-83b5-84f764dd902f

import Mathlib
import Definitions.Def_SetOptLattice_Existence_Model

open SetOptLattice.Existence
namespace Aux_SetOptLattice_P23
open SetOptLattice.Existence

theorem anti {Z : Type*} (ψ : Z → EReal) {D E : Set Z} (h : D ⊆ E) :
    infExt ψ E ≤ infExt ψ D := by
  unfold infExt
  exact biInf_mono h

theorem sub_cl {Z : Type*} (Ψ : Set (Z → EReal)) (D : Set Z) : D ⊆ clPsi Ψ D := by
  intro z hz ψ _
  unfold infExt
  exact biInf_le _ hz

theorem mem_of_closed {Z : Type*} (Ψ : Set (Z → EReal)) {D E : Set Z} (hD : IsPsiClosed Ψ D)
    (z : Z) (h : ∀ ψ ∈ Ψ, infExt ψ E ≤ ψ z) (hDE : E ⊆ D) : z ∈ D := by
  rw [← hD]
  intro ψ hψ
  exact le_trans (anti ψ hDE) (h ψ hψ)

theorem inf_cl {Z : Type*} (Ψ : Set (Z → EReal)) (D : Set Z) (ψ : Z → EReal) (hψ : ψ ∈ Ψ) :
    infExt ψ (clPsi Ψ D) = infExt ψ D := by
  apply le_antisymm (anti ψ (sub_cl Ψ D))
  unfold infExt
  exact le_iInf₂ (fun z hz => hz ψ hψ)

theorem cl_closed {Z : Type*} (Ψ : Set (Z → EReal)) (D : Set Z) :
    IsPsiClosed Ψ (clPsi Ψ D) := by
  unfold IsPsiClosed
  ext z
  constructor
  · intro hz ψ hψ
    have := hz ψ hψ
    rwa [inf_cl Ψ D ψ hψ] at this
  · intro hz
    exact sub_cl Ψ _ hz

end Aux_SetOptLattice_P23

open Set Filter Topology
open scoped Pointwise


theorem solution {Z : Type*} [Preorder Z] (Ψ : Set (Z → EReal))
    (hΨ : ∀ ψ ∈ Ψ, Monotone ψ) :
    (∀ D E : Set Z, IsPsiClosed Ψ D → IsPsiClosed Ψ E → (SetLE Ψ D E ↔ E ⊆ D)) ∧
      ∀ 𝒜 : Set (Set Z), (∀ A ∈ 𝒜, IsPsiClosed Ψ A) →
        (IsPsiClosed Ψ (latInf Ψ 𝒜) ∧ (∀ A ∈ 𝒜, A ⊆ latInf Ψ 𝒜) ∧
            ∀ C : Set Z, IsPsiClosed Ψ C → (∀ A ∈ 𝒜, A ⊆ C) → latInf Ψ 𝒜 ⊆ C) ∧
          (IsPsiClosed Ψ (⋂₀ 𝒜) ∧ (∀ A ∈ 𝒜, ⋂₀ 𝒜 ⊆ A) ∧
            ∀ C : Set Z, IsPsiClosed Ψ C → (∀ A ∈ 𝒜, C ⊆ A) → C ⊆ ⋂₀ 𝒜) := by
  open Aux_SetOptLattice_P23 in
  refine ⟨fun D E hD hE => ⟨fun h => ?_, fun h ψ _ => anti ψ h⟩, fun 𝒜 h𝒜 => ⟨⟨cl_closed Ψ _, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩⟩
  · intro z hz
    exact mem_of_closed Ψ hD z (fun ψ hψ => le_trans (h ψ hψ) (sub_cl Ψ E hz ψ hψ)) le_rfl
  · intro A hA
    exact le_trans (subset_sUnion_of_mem hA) (sub_cl Ψ _)
  · intro C hC hAC z hz
    exact mem_of_closed Ψ hC z hz (sUnion_subset hAC)
  · unfold IsPsiClosed
    apply Subset.antisymm _ (sub_cl Ψ _)
    intro z hz
    refine mem_sInter.mpr (fun A hA => ?_)
    exact mem_of_closed Ψ (h𝒜 A hA) z hz (sInter_subset_of_mem hA)
  · intro A hA
    exact sInter_subset_of_mem hA
  · intro C _ hCA
    exact subset_sInter hCA
