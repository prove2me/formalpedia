-- Prove2me | solution 1 for TangleStructTree.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T06:32:19.363194+00:00
-- url     : https://prove2.me/submissions/75e6e672-fb72-4b0d-9705-1c8e742be975

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem
import Definitions.Def_TangleStructTree_IsOrientation
import Definitions.Def_TangleStructTree_IsConsistent
import Definitions.Def_TangleStructTree_sepClosure
import Definitions.Def_TangleStructTree_SepTree

section
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TangleStructTree.Dev.Base

open TangleStructTree SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma mem_labels {v : List E} {x : E} : x ∈ labels v ↔ x ∈ v := Iff.rfl

lemma labels_cons (x : E) (v : List E) : labels (x :: v) = insert x (labels v) := by
  ext y; simp [labels]

lemma labels_nil : labels ([] : List E) = ∅ := by
  ext y; simp [labels]

lemma nodes_append (T : SepTree E) : ∀ (a w : List E), a ++ w ∈ T.nodes → w ∈ T.nodes := by
  intro a
  induction a with
  | nil => intro w h; simpa using h
  | cons x a ih => intro w h; exact ih w (T.parent_mem x _ h)

end TangleStructTree.Dev.Base
end

section
set_option autoImplicit false

namespace TangleStructTree.Dev.L32

open TangleStructTree SepSystem TangleStructTree.Dev.Base

variable {E : Type*} [PartialOrder E] [SepSystem E]

lemma comparable (T : SepTree E) (τ : Set E) (hτ : IsOrientation τ) :
    ∀ w ∈ T.nodes, labels w ⊆ τ → ∀ v ∈ T.nodes, labels v ⊆ τ → v <:+ w ∨ w <:+ v := by
  intro w
  induction w with
  | nil => intro _ _ v _ _; exact Or.inr List.nil_suffix
  | cons y w' ih =>
    intro hw hwτ v hv hvτ
    have hw' := T.parent_mem y w' hw
    have hw'τ : labels w' ⊆ τ := fun z hz => hwτ (by rw [labels_cons]; exact Set.mem_insert_of_mem _ hz)
    have hyτ : y ∈ τ := hwτ (by rw [labels_cons]; exact Set.mem_insert _ _)
    rcases ih hw' hw'τ v hv hvτ with h | h
    · exact Or.inl (h.trans (List.suffix_cons y w'))
    · obtain ⟨t, rfl⟩ := h
      rcases List.eq_nil_or_concat t with rfl | ⟨L, b, rfl⟩
      · exact Or.inl (by simpa using List.suffix_cons y w')
      · simp only [List.concat_eq_append] at hv hvτ ⊢
        have hbv : b ∈ labels ((L ++ [b]) ++ w') := by
          rw [mem_labels]; simp
        have hb : b :: w' ∈ T.nodes := by
          have : (L ++ [b]) ++ w' = L ++ b :: w' := by simp
          rw [this] at hv
          exact nodes_append T L _ hv
        have hbτ : b ∈ τ := hvτ hbv
        obtain ⟨s, hs, hsy⟩ := T.split w' hw' ⟨y, hw⟩
        have hys := (hs y).mp hw
        have hbs := (hs b).mp hb
        have hby : b = y := by
          by_contra hne
          have hrev : b = rev y := by
            rcases hys with h1 | h1 <;> rcases hbs with h2 | h2
            · exact absurd (h2.trans h1.symm) hne
            · rw [h2, h1]
            · rw [h2, h1, rev_rev]
            · exact absurd (h2.trans h1.symm) hne
          have := (hτ y).2 hyτ (hrev ▸ hbτ)
          exact hne (hrev.trans this)
        subst hby
        exact Or.inr ⟨L, by simp⟩

lemma exists_leaf (T : SepTree E) (τ : Set E) (hτ : IsOrientation τ) :
    ∃ ℓ, T.IsLeaf ℓ ∧ labels ℓ ⊆ τ := by
  classical
  have hne : (T.nodes.filter fun v => labels v ⊆ τ).Nonempty :=
    ⟨[], Finset.mem_filter.mpr ⟨T.root_mem, by rw [labels_nil]; exact Set.empty_subset _⟩⟩
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image _ List.length hne
  obtain ⟨hvn, hvτ⟩ := Finset.mem_filter.mp hv
  refine ⟨v, ⟨hvn, ?_⟩, hvτ⟩
  intro x hx
  obtain ⟨s, hs, -⟩ := T.split v hvn ⟨x, hx⟩
  have key : ∃ z, z :: v ∈ T.nodes ∧ z ∈ τ := by
    rcases (hτ s).1 with h | h
    · exact ⟨s, (hs s).mpr (Or.inl rfl), h⟩
    · exact ⟨rev s, (hs (rev s)).mpr (Or.inr rfl), h⟩
  obtain ⟨z, hz, hzτ⟩ := key
  have := hmax (z :: v) (Finset.mem_filter.mpr ⟨hz, by
    rw [labels_cons]; exact Set.insert_subset hzτ hvτ⟩)
  simp at this

end TangleStructTree.Dev.L32

namespace TangleStructTree
open SepSystem TangleStructTree.Dev.Base TangleStructTree.Dev.L32

variable {E : Type*} [PartialOrder E] [SepSystem E]

theorem chk_lemma_3_2 (T : SepTree E) (τ : Set E) (hτ : IsOrientation τ) :
    ∃! ℓ : List E, T.IsLeaf ℓ ∧ labels ℓ ⊆ τ := by
  obtain ⟨ℓ, hℓ, hℓτ⟩ := exists_leaf T τ hτ
  refine ⟨ℓ, ⟨hℓ, hℓτ⟩, ?_⟩
  rintro ℓ' ⟨hℓ', hℓ'τ⟩
  have key : ∀ a b : List E, T.IsLeaf a → T.IsLeaf b → labels a ⊆ τ → labels b ⊆ τ →
      a <:+ b → a = b := by
    intro a b ha hb haτ hbτ ⟨t, ht⟩
    rcases List.eq_nil_or_concat t with rfl | ⟨L, c, rfl⟩
    · simpa using ht
    · exfalso
      simp only [List.concat_eq_append] at ht
      have : (L ++ [c]) ++ a = L ++ c :: a := by simp
      rw [this] at ht
      have hbn := hb.1
      rw [← ht] at hbn
      exact ha.2 c (nodes_append T L _ hbn)
  rcases comparable T τ hτ ℓ' hℓ'.1 hℓ'τ ℓ hℓ.1 hℓτ with h | h
  · exact (key ℓ ℓ' hℓ hℓ' hℓτ hℓ'τ h).symm
  · exact key ℓ' ℓ hℓ' hℓ hℓ'τ hℓτ h

end TangleStructTree
end

theorem solution : type_of% @TangleStructTree.chk_lemma_3_2 := @TangleStructTree.chk_lemma_3_2
