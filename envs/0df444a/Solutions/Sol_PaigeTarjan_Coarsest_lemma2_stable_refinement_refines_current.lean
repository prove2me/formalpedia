-- Prove2me | solution 1 for PaigeTarjan.Coarsest.lemma2_stable_refinement_refines_current
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T07:44:12.04078+00:00
-- url     : https://prove2.me/submissions/d767b20e-18b1-485b-aaa8-c4dab154d77a

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic
import Definitions.Def_PaigeTarjan_Coarsest_Algorithms

set_option autoImplicit false

/-! ## Basic facts about preimages, partitions and `split` -/

open PaigeTarjan.Coarsest in
theorem pt97_mem_preimage {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (x : U) :
    x ∈ preimage E T ↔ ∃ y ∈ T, E x y := by
  simp [preimage]

open PaigeTarjan.Coarsest in
theorem pt97_part_eq {U : Type*} [Fintype U] [DecidableEq U]
    {X : Finset (Finset U)} (hX : IsPartition X) {A C : Finset U} (hA : A ∈ X) (hC : C ∈ X)
    {x : U} (hxA : x ∈ A) (hxC : x ∈ C) : A = C := by
  by_contra h
  exact Finset.disjoint_left.1 (hX.2.1 A hA C hC h) hxA hxC

open PaigeTarjan.Coarsest in
theorem pt97_mem_split {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U))
    (C : Finset U) :
    C ∈ split E T Q ↔
      ∃ A ∈ Q, (C = A ∩ preimage E T ∨ C = A \ preimage E T) ∧ C.Nonempty := by
  simp only [split, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton]

open PaigeTarjan.Coarsest in
theorem pt97_split_sub {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U))
    {C : Finset U} (hC : C ∈ split E T Q) : ∃ A ∈ Q, C ⊆ A := by
  obtain ⟨A, hA, h, -⟩ := (pt97_mem_split E T Q C).1 hC
  refine ⟨A, hA, ?_⟩
  rcases h with rfl | rfl
  · exact Finset.inter_subset_left
  · exact Finset.sdiff_subset

open PaigeTarjan.Coarsest in
theorem pt97_split_refines {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U)) :
    Refines (split E T Q) Q :=
  fun _ hC => pt97_split_sub E T Q hC

open PaigeTarjan.Coarsest in
theorem pt97_split_partition {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U))
    (hQ : IsPartition Q) : IsPartition (split E T Q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨A, -, -, hne⟩ := (pt97_mem_split E T Q C).1 hC
    exact hne
  · intro C hC D hD hCD
    obtain ⟨A, hA, hCA, -⟩ := (pt97_mem_split E T Q C).1 hC
    obtain ⟨A', hA', hDA, -⟩ := (pt97_mem_split E T Q D).1 hD
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
    · refine ⟨A ∩ preimage E T, (pt97_mem_split E T Q _).2
        ⟨A, hA, Or.inl rfl, ⟨x, Finset.mem_inter.2 ⟨hx, hp⟩⟩⟩, Finset.mem_inter.2 ⟨hx, hp⟩⟩
    · refine ⟨A \ preimage E T, (pt97_mem_split E T Q _).2
        ⟨A, hA, Or.inr rfl, ⟨x, Finset.mem_sdiff.2 ⟨hx, hp⟩⟩⟩, Finset.mem_sdiff.2 ⟨hx, hp⟩⟩

open PaigeTarjan.Coarsest in
theorem pt97_split_stable {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U)) :
    StableWrt E (split E T Q) T := by
  intro C hC
  obtain ⟨A, -, h, -⟩ := (pt97_mem_split E T Q C).1 hC
  unfold StableBlock
  rcases h with rfl | rfl
  · left; exact Finset.inter_subset_right
  · right
    rw [Finset.disjoint_left]
    intro x hx
    exact (Finset.mem_sdiff.1 hx).2

open PaigeTarjan.Coarsest in
theorem pt97_stable_mono {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] {Q Q' : Finset (Finset U)} {T : Finset U}
    (h : Refines Q' Q) (hs : StableWrt E Q T) : StableWrt E Q' T := by
  intro C hC
  obtain ⟨A, hA, hCA⟩ := h C hC
  have hA' := hs A hA
  unfold StableBlock at hA' ⊢
  rcases hA' with h1 | h1
  · left; exact hCA.trans h1
  · right; exact h1.mono_left hCA

open PaigeTarjan.Coarsest in
theorem pt97_refines_trans {U : Type*} [Fintype U] [DecidableEq U]
    {R Q P : Finset (Finset U)} (h1 : Refines R Q) (h2 : Refines Q P) : Refines R P := by
  intro D hD
  obtain ⟨A, hA, hDA⟩ := h1 D hD
  obtain ⟨C, hC, hAC⟩ := h2 A hA
  exact ⟨C, hC, hDA.trans hAC⟩

open PaigeTarjan.Coarsest in
theorem pt97_refines_split {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] {R Q : Finset (Finset U)} {T : Finset U}
    (hR : IsPartition R) (hRQ : Refines R Q) (hs : StableWrt E R T) :
    Refines R (split E T Q) := by
  intro D hD
  obtain ⟨A, hA, hDA⟩ := hRQ D hD
  obtain ⟨x, hx⟩ := hR.1 D hD
  have hsD := hs D hD
  unfold StableBlock at hsD
  rcases hsD with h | h
  · refine ⟨A ∩ preimage E T, (pt97_mem_split E T Q _).2
      ⟨A, hA, Or.inl rfl, ⟨x, Finset.mem_inter.2 ⟨hDA hx, h hx⟩⟩⟩, ?_⟩
    exact Finset.subset_inter hDA h
  · refine ⟨A \ preimage E T, (pt97_mem_split E T Q _).2
      ⟨A, hA, Or.inr rfl, ⟨x, Finset.mem_sdiff.2 ⟨hDA hx, Finset.disjoint_left.1 h hx⟩⟩⟩, ?_⟩
    intro y hy
    exact Finset.mem_sdiff.2 ⟨hDA hy, Finset.disjoint_left.1 h hy⟩

open PaigeTarjan.Coarsest in
theorem pt97_stable_of_sat {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] {R : Finset (Finset U)} {T : Finset U}
    (hR : IsPartition R) (hst : Stable E R) (hsat : ∀ D ∈ R, D ⊆ T ∨ Disjoint D T) :
    StableWrt E R T := by
  intro D hD
  unfold StableBlock
  by_cases hex : ∃ x ∈ D, x ∈ preimage E T
  · obtain ⟨x, hxD, hxp⟩ := hex
    obtain ⟨y, hyT, hxy⟩ := (pt97_mem_preimage E T x).1 hxp
    obtain ⟨D', hD', hyD'⟩ := hR.2.2 y
    have hD'T : D' ⊆ T := by
      rcases hsat D' hD' with h | h
      · exact h
      · exact absurd hyT (Finset.disjoint_left.1 h hyD')
    have hDD' := hst D' hD' D hD
    unfold StableBlock at hDD'
    rcases hDD' with h | h
    · left
      intro z hz
      obtain ⟨w, hw, hzw⟩ := (pt97_mem_preimage E D' z).1 (h hz)
      exact (pt97_mem_preimage E T z).2 ⟨w, hD'T hw, hzw⟩
    · exact absurd ((pt97_mem_preimage E D' x).2 ⟨y, hyD', hxy⟩) (Finset.disjoint_left.1 h hxD)
  · right
    rw [Finset.disjoint_left]
    intro x hx hxp
    exact hex ⟨x, hx, hxp⟩

open PaigeTarjan.Coarsest in
theorem pt97_card_le {U : Type*} [Fintype U] [DecidableEq U]
    {X : Finset (Finset U)} (hX : IsPartition X) : X.card ≤ Fintype.card U := by
  have hdisj : (X : Set (Finset U)).PairwiseDisjoint id := by
    intro A hA B hB h
    exact hX.2.1 A hA B hB h
  calc X.card = ∑ _T ∈ X, 1 := by simp
    _ ≤ ∑ T ∈ X, T.card := Finset.sum_le_sum (fun T hT => Finset.card_pos.2 (hX.1 T hT))
    _ = (X.biUnion id).card := (Finset.card_biUnion hdisj).symm
    _ ≤ Fintype.card U := Finset.card_le_univ _


/-! ## Lemma 2 -/

open PaigeTarjan.Coarsest in
theorem pt97_union_sat {U : Type*} [Fintype U] [DecidableEq U]
    {Q R : Finset (Finset U)} {S : Finset U} (hQ : IsPartition Q) (hRQ : Refines R Q)
    (hS : IsUnionOfBlocks S Q) : ∀ D ∈ R, D ⊆ S ∨ Disjoint D S := by
  obtain ⟨T, hTQ, rfl⟩ := hS
  intro D hD
  obtain ⟨A, hA, hDA⟩ := hRQ D hD
  by_cases hAT : A ∈ T
  · left
    intro x hx
    exact Finset.mem_biUnion.2 ⟨A, hAT, hDA hx⟩
  · right
    rw [Finset.disjoint_left]
    intro x hx hxS
    obtain ⟨C, hCT, hxC⟩ := Finset.mem_biUnion.1 hxS
    have hAC : A ≠ C := fun h => hAT (h ▸ hCT)
    exact Finset.disjoint_left.1 (hQ.2.1 A hA C (hTQ hCT) hAC) (hDA hx) hxC

open PaigeTarjan.Coarsest in
theorem solution {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (P : Finset (Finset U)) (hP : IsPartition P)
    (K : ℕ) (Qs : Fin (K + 1) → Finset (Finset U)) (hrun : IsNaiveRun E P K Qs)
    (R : Finset (Finset U)) (hR : IsPartition R) (hRP : Refines R P) (hRs : Stable E R) :
    ∀ j : Fin (K + 1), Refines R (Qs j) := by
  obtain ⟨h0, hsteps⟩ := hrun
  have key : ∀ i (hi : i < K + 1), IsPartition (Qs ⟨i, hi⟩) ∧ Refines R (Qs ⟨i, hi⟩) := by
    intro i
    induction i with
    | zero =>
      intro hi
      have : Qs ⟨0, hi⟩ = P := h0
      rw [this]
      exact ⟨hP, hRP⟩
    | succ i ih =>
      intro hi
      obtain ⟨hQ, hRQ⟩ := ih (by omega)
      have hst := hsteps ⟨i, by omega⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hst
      obtain ⟨S, hSu, -, hQ'⟩ := hst
      rw [hQ']
      exact ⟨pt97_split_partition E S _ hQ,
        pt97_refines_split E hR hRQ (pt97_stable_of_sat E hR hRs (pt97_union_sat hQ hRQ hSu))⟩
  intro j
  exact (key j.1 j.2).2
