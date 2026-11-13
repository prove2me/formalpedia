-- Prove2me | solution 1 for TangleStructTree.lemma_4_7
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:45:13.178497+00:00
-- url     : https://prove2.me/submissions/c02ae954-9965-45db-b8f8-4bd525130fca

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_SepTree
import Definitions.Def_TangleStructTree_SepTree_ThoroughlyOrdered
import Theorems.Thm_TangleStructTree_closure_eq
import Theorems.Thm_TangleStructTree_lemma_2_1
import Definitions.Def_TangleStructTree_IsTangle
import Definitions.Def_TangleStructTree_IsOrderFunction
import Definitions.Def_TangleStructTree_OrderInjective
import Definitions.Def_TangleStructTree_StronglyEfficient
import Definitions.Def_TangleStructTree_IsRich
import Definitions.Def_TangleStructTree_SepTree_Consistent
import Definitions.Def_TangleStructTree_SepTree_IsTST
import Theorems.Thm_TangleStructTree_lemma_3_2
import Theorems.Thm_TangleStructTree_lemma_4_2
import Theorems.Thm_TangleStructTree_efficient_strongly_of_injective

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TangleStructTree.Dev.Base

open TangleStructTree SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma le_rev_symm {a b : E} (h : a ≤ rev b) : b ≤ rev a := by
  have := SepSystem.rev_le_rev _ _ h
  rwa [rev_rev] at this

lemma consistent_empty : IsConsistent (∅ : Set E) := fun x hx => absurd hx (by simp)

lemma labels_cons (x : E) (v : List E) : labels (x :: v) = insert x (labels v) := by
  ext y; simp [labels]

lemma labels_nil : labels ([] : List E) = ∅ := by
  ext y; simp [labels]

end TangleStructTree.Dev.Base
end

section
set_option autoImplicit false

namespace TangleStructTree.Dev.Cl

open TangleStructTree SepSystem TangleStructTree.Dev.Base

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma mem_cl (τ : Set E) (hτ : IsConsistent τ) {x : E} :
    x ∈ sepClosure τ ↔ x ∈ τ ∨ ∃ r ∈ τ, (r ≠ x ∧ r ≠ rev x) ∧ r < x := by
  rw [(TangleStructTree.closure_eq τ hτ).2]
  simp [Set.mem_union]

lemma sub_cl (τ : Set E) : τ ⊆ sepClosure τ := fun _ h => Or.inl h

lemma not_orients_mem {τ : Set E} {x : E} (h : ¬ Orients τ x) : x ∉ τ ∧ rev x ∉ τ :=
  ⟨fun h' => h (Or.inl h'), fun h' => h (Or.inr h')⟩

lemma thor_consistent (ord : E → ℝ) (T : SepTree E) (hT : T.ThoroughlyOrdered ord) :
    ∀ v ∈ T.nodes, IsConsistent (labels v) := by
  intro v
  induction v with
  | nil => intro _; rw [labels_nil]; exact consistent_empty
  | cons x u ih =>
    intro hx
    have hu := T.parent_mem x u hx
    have hβ := ih hu
    obtain ⟨hno, -⟩ := hT u x hx
    obtain ⟨hx1, hx2⟩ := not_orients_mem hno
    have hxβ : x ∉ labels u := fun h => hx1 (sub_cl _ h)
    have hrxβ : rev x ∉ labels u := fun h => hx2 (sub_cl _ h)
    -- no element of β is below x or rev x
    have h1 : ∀ r ∈ labels u, r ≠ x → r ≠ rev x → ¬ r < x := by
      intro r hr h1 h2 hlt
      exact hx1 ((mem_cl _ hβ).mpr (Or.inr ⟨r, hr, ⟨h1, h2⟩, hlt⟩))
    have h2 : ∀ r ∈ labels u, r ≠ rev x → r ≠ x → ¬ r < rev x := by
      intro r hr h1 h2 hlt
      exact hx2 ((mem_cl _ hβ).mpr (Or.inr ⟨r, hr, ⟨h1, by rw [rev_rev]; exact h2⟩, hlt⟩))
    rw [labels_cons]
    intro a ha b hb hba hbra hab
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hba (hb.trans ha.symm)
    · have h3 : b ≤ rev x := by rw [← ha]; exact le_rev_symm hab
      have h4 : b ≠ rev x := fun h => hrxβ (h ▸ hb)
      exact h2 b hb h4 (fun h => hba (h.trans ha.symm)) (lt_of_le_of_ne h3 h4)
    · have h3 : a ≤ rev x := by rw [← hb]; exact hab
      have h4 : a ≠ rev x := fun h => hrxβ (h ▸ ha)
      exact h2 a ha h4 (fun h => hba (hb.trans h.symm)) (lt_of_le_of_ne h3 h4)
    · exact hβ a ha b hb hba hbra hab

end TangleStructTree.Dev.Cl
end

section
set_option autoImplicit false

namespace TangleStructTree

open SepSystem TangleStructTree.Dev.Base TangleStructTree.Dev.Cl

variable {E : Type*} [PartialOrder E] [SepSystem E]

theorem chk_lemma_4_7 (ord : E → ℝ) (hord : IsOrderFunction ord) (hinj : OrderInjective ord)
    (ℱ : Set (Set E)) (hT : ∃ T : SepTree E, T.ThoroughlyOrdered ord ∧ T.IsTST ℱ) :
    IsRich ord ℱ := by
  obtain ⟨T, hthor, hcon, hleaf, hnl⟩ := hT
  intro τ hτ hτc hnav
  obtain ⟨ℓ, ⟨hℓ, hℓτ⟩, -⟩ := TangleStructTree.lemma_3_2 T τ hτ
  have hcℓ := thor_consistent ord T hthor ℓ hℓ.1
  have h21 := TangleStructTree.lemma_2_1 (labels ℓ) τ hℓτ hcℓ hτc
  have hCτ : sepClosure (labels ℓ) ⊆ τ := by
    intro x hx
    have := h21.1 hx
    rwa [h21.2 hτ] at this
  have hpart : IsPartialOrientation τ := fun x hx hrx => (hτ x).2 hx hrx
  rcases hleaf ℓ hℓ with ⟨-, hTangle⟩ | ⟨-, hforb⟩
  · exfalso
    have hτC : τ ⊆ sepClosure (labels ℓ) := by
      intro x hx
      rcases (hTangle.1 x).1 with h | h
      · exact h
      · have := (hτ x).2 hx (hCτ h)
        rw [this] at h; exact h
    apply hnav
    have : sepClosure (labels ℓ) = τ := Set.Subset.antisymm hCτ hτC
    rw [← this]; exact hTangle.2.2
  · unfold Avoids at hforb
    push_neg at hforb
    obtain ⟨σ, hσ, hσsub⟩ := hforb
    have hlem := (TangleStructTree.lemma_4_2 ord hord T hthor ℓ hℓ.1).2 hcℓ τ hpart hCτ
    have heff : Efficient ord σ τ :=
      ⟨hσsub.trans hlem.1, fun x hx y hy => hlem.2 x (hσsub hx) y hy⟩
    exact ⟨σ, hσ, TangleStructTree.efficient_strongly_of_injective ord hord hinj τ σ hpart heff⟩

end TangleStructTree
end

theorem solution : type_of% @TangleStructTree.chk_lemma_4_7 := @TangleStructTree.chk_lemma_4_7
