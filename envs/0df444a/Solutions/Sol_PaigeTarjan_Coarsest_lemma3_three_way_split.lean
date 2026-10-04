-- Prove2me | solution 1 for PaigeTarjan.Coarsest.lemma3_three_way_split
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T17:52:55.258977+00:00
-- url     : https://prove2.me/submissions/f4cb59d6-bb4e-4e58-bab6-eca9272f3b75

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic

set_option autoImplicit false

open PaigeTarjan.Coarsest in
theorem ptc7_mem_preimage {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (x : U) :
    x ∈ preimage E T ↔ ∃ y ∈ T, E x y := by
  simp [preimage]

open PaigeTarjan.Coarsest in
theorem ptc7_part_eq {U : Type*} [Fintype U] [DecidableEq U]
    {X : Finset (Finset U)} (hX : IsPartition X) {A C : Finset U} (hA : A ∈ X) (hC : C ∈ X)
    {x : U} (hxA : x ∈ A) (hxC : x ∈ C) : A = C := by
  by_contra h
  exact Finset.disjoint_left.1 (hX.2.1 A hA C hC h) hxA hxC

open PaigeTarjan.Coarsest in
theorem ptc7_mem_split {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U))
    (C : Finset U) :
    C ∈ split E T Q ↔
      ∃ A ∈ Q, (C = A ∩ preimage E T ∨ C = A \ preimage E T) ∧ C.Nonempty := by
  simp only [split, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton]

open PaigeTarjan.Coarsest in
theorem ptc7_split_sub {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U))
    {C : Finset U} (hC : C ∈ split E T Q) : ∃ A ∈ Q, C ⊆ A := by
  obtain ⟨A, hA, h, -⟩ := (ptc7_mem_split E T Q C).1 hC
  refine ⟨A, hA, ?_⟩
  rcases h with rfl | rfl
  · exact Finset.inter_subset_left
  · exact Finset.sdiff_subset

open PaigeTarjan.Coarsest in
theorem ptc7_split_refines {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U)) :
    Refines (split E T Q) Q :=
  fun _ hC => ptc7_split_sub E T Q hC

open PaigeTarjan.Coarsest in
theorem ptc7_split_partition {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U))
    (hQ : IsPartition Q) : IsPartition (split E T Q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨A, -, -, hne⟩ := (ptc7_mem_split E T Q C).1 hC
    exact hne
  · intro C hC D hD hCD
    obtain ⟨A, hA, hCA, -⟩ := (ptc7_mem_split E T Q C).1 hC
    obtain ⟨A', hA', hDA, -⟩ := (ptc7_mem_split E T Q D).1 hD
    by_cases hAA : A = A'
    · subst hAA
      rw [Finset.disjoint_left]
      intro x h1 h2
      rcases hCA with rfl | rfl <;> rcases hDA with rfl | rfl
      · exact hCD rfl
      · simp only [Finset.mem_inter, Finset.mem_sdiff] at h1 h2; exact h2.2 h1.2
      · simp only [Finset.mem_inter, Finset.mem_sdiff] at h1 h2; exact h1.2 h2.2
      · exact hCD rfl
    · have hCsub : C ⊆ A := by
        rcases hCA with rfl | rfl
        · exact Finset.inter_subset_left
        · exact Finset.sdiff_subset
      have hDsub : D ⊆ A' := by
        rcases hDA with rfl | rfl
        · exact Finset.inter_subset_left
        · exact Finset.sdiff_subset
      exact (hQ.2.1 A hA A' hA' hAA).mono hCsub hDsub
  · intro x
    obtain ⟨A, hA, hx⟩ := hQ.2.2 x
    by_cases hp : x ∈ preimage E T
    · refine ⟨A ∩ preimage E T, (ptc7_mem_split E T Q _).2
        ⟨A, hA, Or.inl rfl, ⟨x, Finset.mem_inter.2 ⟨hx, hp⟩⟩⟩, Finset.mem_inter.2 ⟨hx, hp⟩⟩
    · refine ⟨A \ preimage E T, (ptc7_mem_split E T Q _).2
        ⟨A, hA, Or.inr rfl, ⟨x, Finset.mem_sdiff.2 ⟨hx, hp⟩⟩⟩, Finset.mem_sdiff.2 ⟨hx, hp⟩⟩


open PaigeTarjan.Coarsest in
theorem ptc7_ne_of_mem_split {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (X : Finset (Finset U))
    {C : Finset U} (hC : C ∈ split E T X) : C.Nonempty :=
  ((ptc7_mem_split E T X C).1 hC).choose_spec.2.2

open PaigeTarjan.Coarsest in
theorem ptc7_both {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (X : Finset (Finset U))
    (hX : IsPartition X) {A : Finset U} (hA : A ∈ X)
    (h1 : (A ∩ preimage E T).Nonempty) (h2 : (A \ preimage E T).Nonempty) :
    A ∉ split E T X ∧ A ∩ preimage E T ∈ split E T X ∧ A \ preimage E T ∈ split E T X := by
  refine ⟨?_, (ptc7_mem_split E T X _).2 ⟨A, hA, Or.inl rfl, h1⟩,
    (ptc7_mem_split E T X _).2 ⟨A, hA, Or.inr rfl, h2⟩⟩
  intro hmem
  obtain ⟨C, hC, hAC, hne⟩ := (ptc7_mem_split E T X A).1 hmem
  have hsub : A ⊆ C := by
    rcases hAC with h | h <;> rw [h]
    · exact Finset.inter_subset_left
    · exact Finset.sdiff_subset
  obtain ⟨x, hx⟩ := hne
  have hCA : C = A := ptc7_part_eq hX hC hA (hsub hx) hx
  subst hCA
  rcases hAC with h | h
  · obtain ⟨y, hy⟩ := h2
    rw [Finset.mem_sdiff] at hy
    have : y ∈ C ∩ preimage E T := h ▸ hy.1
    exact hy.2 (Finset.mem_inter.1 this).2
  · obtain ⟨y, hy⟩ := h1
    rw [Finset.mem_inter] at hy
    have : y ∈ C \ preimage E T := h ▸ hy.1
    exact (Finset.mem_sdiff.1 this).2 hy.2

open PaigeTarjan.Coarsest in
theorem solution {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (Q : Finset (Finset U)) (S B D : Finset U)
    (hQ : IsPartition Q) (hSQ : IsUnionOfBlocks S Q) (hstab : StableWrt E Q S)
    (hB : B ∈ Q) (hBS : B ⊆ S) (hD : D ∈ Q) :
    let D₁ := D ∩ preimage E B
    let D₂ := D \ D₁
    let D₁₁ := D₁ ∩ preimage E (S \ B)
    let D₁₂ := D₁ \ D₁₁
    ((D ∉ split E B Q ∧ D₁ ∈ split E B Q ∧ D₂ ∈ split E B Q) ↔
        ((D ∩ preimage E B).Nonempty ∧ (D \ preimage E B).Nonempty)) ∧
    ((D₁ ∉ split E (S \ B) (split E B Q) ∧ D₁₁ ∈ split E (S \ B) (split E B Q) ∧
        D₁₂ ∈ split E (S \ B) (split E B Q)) ↔
        ((D₁ ∩ preimage E (S \ B)).Nonempty ∧ (D₁ \ preimage E (S \ B)).Nonempty)) ∧
    (D₂ ∈ split E B Q → D₂ ∈ split E (S \ B) (split E B Q)) ∧
    D₁₂ = D₁ ∩ (preimage E B \ preimage E (S \ B)) := by
  dsimp only
  have hsd : ∀ (A P : Finset U), A \ (A ∩ P) = A \ P := by
    intro A P; ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto
  have hQ1 : IsPartition (split E B Q) := ptc7_split_partition E B Q hQ
  rw [hsd, hsd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨-, h1, h2⟩
      exact ⟨ptc7_ne_of_mem_split E B Q h1, ptc7_ne_of_mem_split E B Q h2⟩
    · rintro ⟨h1, h2⟩
      exact ptc7_both E B Q hQ hD h1 h2
  · constructor
    · rintro ⟨-, h1, h2⟩
      exact ⟨ptc7_ne_of_mem_split E _ _ h1, ptc7_ne_of_mem_split E _ _ h2⟩
    · rintro ⟨h1, h2⟩
      have hD1ne : (D ∩ preimage E B).Nonempty := by
        obtain ⟨x, hx⟩ := h1
        exact ⟨x, (Finset.mem_inter.1 hx).1⟩
      have hD1 : D ∩ preimage E B ∈ split E B Q :=
        (ptc7_mem_split E B Q _).2 ⟨D, hD, Or.inl rfl, hD1ne⟩
      exact ptc7_both E (S \ B) (split E B Q) hQ1 hD1 h1 h2
  · intro hD2
    have hne := ptc7_ne_of_mem_split E B Q hD2
    rcases hstab D hD with hsub | hdis
    · have hsub2 : D \ preimage E B ⊆ preimage E (S \ B) := by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        obtain ⟨y, hyS, hxy⟩ := (ptc7_mem_preimage E S x).1 (hsub hx.1)
        rw [ptc7_mem_preimage]
        refine ⟨y, Finset.mem_sdiff.2 ⟨hyS, fun hyB => hx.2 ?_⟩, hxy⟩
        exact (ptc7_mem_preimage E B x).2 ⟨y, hyB, hxy⟩
      refine (ptc7_mem_split E _ _ _).2 ⟨_, hD2, Or.inl (Finset.inter_eq_left.2 hsub2).symm, hne⟩
    · have hmono : preimage E (S \ B) ⊆ preimage E S := by
        intro x hx
        obtain ⟨y, hy, hxy⟩ := (ptc7_mem_preimage E _ x).1 hx
        exact (ptc7_mem_preimage E S x).2 ⟨y, (Finset.mem_sdiff.1 hy).1, hxy⟩
      have hdis2 : Disjoint (D \ preimage E B) (preimage E (S \ B)) :=
        hdis.mono Finset.sdiff_subset hmono
      refine (ptc7_mem_split E _ _ _).2 ⟨_, hD2, Or.inr (Finset.sdiff_eq_self_of_disjoint hdis2).symm, hne⟩
  · ext x
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
