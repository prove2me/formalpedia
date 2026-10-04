-- Prove2me | solution 1 for PaigeTarjan.Coarsest.theorem2_naive_correct
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T18:37:19.562297+00:00
-- url     : https://prove2.me/submissions/cf9c46bf-b7f5-4868-a6fd-010ae4729187

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic
import Definitions.Def_PaigeTarjan_Coarsest_Algorithms

set_option autoImplicit false

/-! ## Basic facts about preimages, partitions and `split` -/

open PaigeTarjan.Coarsest in
theorem pt06_mem_preimage {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (x : U) :
    x ∈ preimage E T ↔ ∃ y ∈ T, E x y := by
  simp [preimage]

open PaigeTarjan.Coarsest in
theorem pt06_part_eq {U : Type*} [Fintype U] [DecidableEq U]
    {X : Finset (Finset U)} (hX : IsPartition X) {A C : Finset U} (hA : A ∈ X) (hC : C ∈ X)
    {x : U} (hxA : x ∈ A) (hxC : x ∈ C) : A = C := by
  by_contra h
  exact Finset.disjoint_left.1 (hX.2.1 A hA C hC h) hxA hxC

open PaigeTarjan.Coarsest in
theorem pt06_mem_split {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U))
    (C : Finset U) :
    C ∈ split E T Q ↔
      ∃ A ∈ Q, (C = A ∩ preimage E T ∨ C = A \ preimage E T) ∧ C.Nonempty := by
  simp only [split, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton]

open PaigeTarjan.Coarsest in
theorem pt06_split_sub {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U))
    {C : Finset U} (hC : C ∈ split E T Q) : ∃ A ∈ Q, C ⊆ A := by
  obtain ⟨A, hA, h, -⟩ := (pt06_mem_split E T Q C).1 hC
  refine ⟨A, hA, ?_⟩
  rcases h with rfl | rfl
  · exact Finset.inter_subset_left
  · exact Finset.sdiff_subset

open PaigeTarjan.Coarsest in
theorem pt06_split_refines {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U)) :
    Refines (split E T Q) Q :=
  fun _ hC => pt06_split_sub E T Q hC

open PaigeTarjan.Coarsest in
theorem pt06_split_partition {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U))
    (hQ : IsPartition Q) : IsPartition (split E T Q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨A, -, -, hne⟩ := (pt06_mem_split E T Q C).1 hC
    exact hne
  · intro C hC D hD hCD
    obtain ⟨A, hA, hCA, -⟩ := (pt06_mem_split E T Q C).1 hC
    obtain ⟨A', hA', hDA, -⟩ := (pt06_mem_split E T Q D).1 hD
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
    · refine ⟨A ∩ preimage E T, (pt06_mem_split E T Q _).2
        ⟨A, hA, Or.inl rfl, ⟨x, Finset.mem_inter.2 ⟨hx, hp⟩⟩⟩, Finset.mem_inter.2 ⟨hx, hp⟩⟩
    · refine ⟨A \ preimage E T, (pt06_mem_split E T Q _).2
        ⟨A, hA, Or.inr rfl, ⟨x, Finset.mem_sdiff.2 ⟨hx, hp⟩⟩⟩, Finset.mem_sdiff.2 ⟨hx, hp⟩⟩

open PaigeTarjan.Coarsest in
theorem pt06_split_stable {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U)) :
    StableWrt E (split E T Q) T := by
  intro C hC
  obtain ⟨A, -, h, -⟩ := (pt06_mem_split E T Q C).1 hC
  unfold StableBlock
  rcases h with rfl | rfl
  · left; exact Finset.inter_subset_right
  · right
    rw [Finset.disjoint_left]
    intro x hx
    exact (Finset.mem_sdiff.1 hx).2

open PaigeTarjan.Coarsest in
theorem pt06_stable_mono {U : Type*} [Fintype U] [DecidableEq U]
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
theorem pt06_refines_trans {U : Type*} [Fintype U] [DecidableEq U]
    {R Q P : Finset (Finset U)} (h1 : Refines R Q) (h2 : Refines Q P) : Refines R P := by
  intro D hD
  obtain ⟨A, hA, hDA⟩ := h1 D hD
  obtain ⟨C, hC, hAC⟩ := h2 A hA
  exact ⟨C, hC, hDA.trans hAC⟩

open PaigeTarjan.Coarsest in
theorem pt06_refines_split {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] {R Q : Finset (Finset U)} {T : Finset U}
    (hR : IsPartition R) (hRQ : Refines R Q) (hs : StableWrt E R T) :
    Refines R (split E T Q) := by
  intro D hD
  obtain ⟨A, hA, hDA⟩ := hRQ D hD
  obtain ⟨x, hx⟩ := hR.1 D hD
  have hsD := hs D hD
  unfold StableBlock at hsD
  rcases hsD with h | h
  · refine ⟨A ∩ preimage E T, (pt06_mem_split E T Q _).2
      ⟨A, hA, Or.inl rfl, ⟨x, Finset.mem_inter.2 ⟨hDA hx, h hx⟩⟩⟩, ?_⟩
    exact Finset.subset_inter hDA h
  · refine ⟨A \ preimage E T, (pt06_mem_split E T Q _).2
      ⟨A, hA, Or.inr rfl, ⟨x, Finset.mem_sdiff.2 ⟨hDA hx, Finset.disjoint_left.1 h hx⟩⟩⟩, ?_⟩
    intro y hy
    exact Finset.mem_sdiff.2 ⟨hDA hy, Finset.disjoint_left.1 h hy⟩

open PaigeTarjan.Coarsest in
theorem pt06_stable_of_sat {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] {R : Finset (Finset U)} {T : Finset U}
    (hR : IsPartition R) (hst : Stable E R) (hsat : ∀ D ∈ R, D ⊆ T ∨ Disjoint D T) :
    StableWrt E R T := by
  intro D hD
  unfold StableBlock
  by_cases hex : ∃ x ∈ D, x ∈ preimage E T
  · obtain ⟨x, hxD, hxp⟩ := hex
    obtain ⟨y, hyT, hxy⟩ := (pt06_mem_preimage E T x).1 hxp
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
      obtain ⟨w, hw, hzw⟩ := (pt06_mem_preimage E D' z).1 (h hz)
      exact (pt06_mem_preimage E T z).2 ⟨w, hD'T hw, hzw⟩
    · exact absurd ((pt06_mem_preimage E D' x).2 ⟨y, hyD', hxy⟩) (Finset.disjoint_left.1 h hxD)
  · right
    rw [Finset.disjoint_left]
    intro x hx hxp
    exact hex ⟨x, hx, hxp⟩

open PaigeTarjan.Coarsest in
theorem pt06_card_le {U : Type*} [Fintype U] [DecidableEq U]
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
theorem pt06_union_sat {U : Type*} [Fintype U] [DecidableEq U]
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
theorem pt06_lemma2 {U : Type*} [Fintype U] [DecidableEq U]
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
      exact ⟨pt06_split_partition E S _ hQ,
        pt06_refines_split E hR hRQ (pt06_stable_of_sat E hR hRs (pt06_union_sat hQ hRQ hSu))⟩
  intro j
  exact (key j.1 j.2).2

/-! ## New facts for Theorem 2 -/

open PaigeTarjan.Coarsest in
theorem pt06_split_eq_of_stable {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (Q : Finset (Finset U)) (S : Finset U)
    (hQ : IsPartition Q) (hs : StableWrt E Q S) : split E S Q = Q := by
  ext C
  rw [pt06_mem_split]
  constructor
  · rintro ⟨A, hA, hC, hne⟩
    rcases hs A hA with h | h
    · rcases hC with rfl | rfl
      · rwa [Finset.inter_eq_left.2 h]
      · exfalso
        rw [Finset.sdiff_eq_empty_iff_subset.2 h] at hne
        exact Finset.not_nonempty_empty hne
    · rcases hC with rfl | rfl
      · exfalso
        rw [Finset.disjoint_iff_inter_eq_empty.1 h] at hne
        exact Finset.not_nonempty_empty hne
      · rwa [Finset.sdiff_eq_self_of_disjoint h]
  · intro hC
    refine ⟨C, hC, ?_, hQ.1 C hC⟩
    rcases hs C hC with h | h
    · exact Or.inl (Finset.inter_eq_left.2 h).symm
    · exact Or.inr (Finset.sdiff_eq_self_of_disjoint h).symm

open PaigeTarjan.Coarsest in
theorem pt06_stable_of_split_eq {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (Q : Finset (Finset U)) (S : Finset U)
    (hQ : IsPartition Q) (heq : split E S Q = Q) : StableWrt E Q S := by
  intro B hB
  by_contra hBs
  unfold StableBlock at hBs
  push_neg at hBs
  obtain ⟨hsub, hndisj⟩ := hBs
  have hI : (B ∩ preimage E S).Nonempty := Finset.not_disjoint_iff_nonempty_inter.1 hndisj
  have hIQ : B ∩ preimage E S ∈ Q := by
    rw [← heq, pt06_mem_split]
    exact ⟨B, hB, Or.inl rfl, hI⟩
  have hne : B ∩ preimage E S ≠ B := by
    intro h
    apply hsub
    rw [← h]
    exact Finset.inter_subset_right
  have hdis := hQ.2.1 _ hIQ B hB hne
  obtain ⟨x, hx⟩ := hI
  exact Finset.disjoint_left.1 hdis hx (Finset.mem_inter.1 hx).1

open PaigeTarjan.Coarsest in
theorem pt06_card_lt_split {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (Q : Finset (Finset U)) (S : Finset U)
    (hQ : IsPartition Q) (hne : split E S Q ≠ Q) : Q.card < (split E S Q).card := by
  set p := preimage E S
  set t : Finset U → Finset (Finset U) :=
    fun B => ({B ∩ p, B \ p} : Finset (Finset U)).filter (fun C => C.Nonempty) with ht
  have hsplit : split E S Q = Q.biUnion t := rfl
  have hdisj : (Q : Set (Finset U)).PairwiseDisjoint t := by
    intro A hA B hB hAB
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro C hCA hCB
    simp only [ht, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hCA hCB
    obtain ⟨hCA, x, hx⟩ := hCA
    obtain ⟨hCB, -⟩ := hCB
    have hxA : x ∈ A := by
      rcases hCA with rfl | rfl
      · exact (Finset.mem_inter.1 hx).1
      · exact (Finset.mem_sdiff.1 hx).1
    have hxB : x ∈ B := by
      rcases hCB with rfl | rfl
      · exact (Finset.mem_inter.1 hx).1
      · exact (Finset.mem_sdiff.1 hx).1
    exact Finset.disjoint_left.1 (hQ.2.1 A hA B hB hAB) hxA hxB
  have hge : ∀ B ∈ Q, 1 ≤ (t B).card := by
    intro B hB
    obtain ⟨x, hx⟩ := hQ.1 B hB
    apply Finset.card_pos.2
    by_cases hp : x ∈ p
    · exact ⟨B ∩ p, by
        simp only [ht, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨by simp, x, Finset.mem_inter.2 ⟨hx, hp⟩⟩⟩
    · exact ⟨B \ p, by
        simp only [ht, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        exact ⟨by simp, x, Finset.mem_sdiff.2 ⟨hx, hp⟩⟩⟩
  have hns : ¬ StableWrt E Q S := fun hs => hne (pt06_split_eq_of_stable E Q S hQ hs)
  have hlt : ∃ B ∈ Q, 1 < (t B).card := by
    unfold StableWrt at hns
    push_neg at hns
    obtain ⟨B, hB, hBs⟩ := hns
    unfold StableBlock at hBs
    push_neg at hBs
    obtain ⟨hsub, hndisj⟩ := hBs
    have hI : (B ∩ p).Nonempty := Finset.not_disjoint_iff_nonempty_inter.1 hndisj
    have hD : (B \ p).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, Ne, Finset.sdiff_eq_empty_iff_subset]
      exact hsub
    have hneq : B ∩ p ≠ B \ p := by
      intro h
      obtain ⟨x, hx⟩ := hI
      have hx2 := hx
      rw [h] at hx2
      exact (Finset.mem_sdiff.1 hx2).2 (Finset.mem_inter.1 hx).2
    refine ⟨B, hB, ?_⟩
    have htB : t B = {B ∩ p, B \ p} := by
      simp only [ht]
      rw [Finset.filter_true_of_mem]
      intro C hC
      simp only [Finset.mem_insert, Finset.mem_singleton] at hC
      rcases hC with rfl | rfl
      · exact hI
      · exact hD
    rw [htB, Finset.card_pair hneq]
    norm_num
  rw [hsplit, Finset.card_biUnion hdisj]
  calc Q.card = ∑ _B ∈ Q, 1 := by simp
    _ < ∑ B ∈ Q, (t B).card := Finset.sum_lt_sum hge hlt

open PaigeTarjan.Coarsest in
theorem pt06_partition_eq {U : Type*} [Fintype U] [DecidableEq U]
    {Q₁ Q₂ : Finset (Finset U)} (h₁ : IsPartition Q₁) (h₂ : IsPartition Q₂)
    (h12 : Refines Q₁ Q₂) (h21 : Refines Q₂ Q₁) : Q₁ ⊆ Q₂ := by
  intro B hB
  obtain ⟨C, hC, hBC⟩ := h12 B hB
  obtain ⟨D, hD, hCD⟩ := h21 C hC
  obtain ⟨x, hx⟩ := h₁.1 B hB
  have hBD : B = D := pt06_part_eq h₁ hB hD hx (hCD (hBC hx))
  subst hBD
  have : B = C := Finset.Subset.antisymm hBC hCD
  rw [this]
  exact hC

open PaigeTarjan.Coarsest in
theorem solution {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    (E : U → U → Prop) [DecidableRel E] (P : Finset (Finset U)) (hP : IsPartition P)
    (K : ℕ) (Qs : Fin (K + 1) → Finset (Finset U)) (hrun : IsNaiveRun E P K Qs) :
    K + 1 ≤ Fintype.card U ∧
    ((¬ ∃ Q', NaiveStep E (Qs (Fin.last K)) Q') →
      IsCoarsestStableRefinement E P (Qs (Fin.last K))) ∧
    (¬ IsCoarsestStableRefinement E P (Qs (Fin.last K)) →
      ∃ Q', NaiveStep E (Qs (Fin.last K)) Q') ∧
    (∀ Q₁ Q₂ : Finset (Finset U), IsCoarsestStableRefinement E P Q₁ →
      IsCoarsestStableRefinement E P Q₂ → Q₁ = Q₂) := by
  have hrun' := hrun
  obtain ⟨h0, hsteps⟩ := hrun
  have key : ∀ i (hi : i < K + 1), IsPartition (Qs ⟨i, hi⟩) ∧ Refines (Qs ⟨i, hi⟩) P ∧
      i + 1 ≤ (Qs ⟨i, hi⟩).card := by
    intro i
    induction i with
    | zero =>
      intro hi
      have : Qs ⟨0, hi⟩ = P := h0
      rw [this]
      refine ⟨hP, fun B hB => ⟨B, hB, le_rfl⟩, ?_⟩
      obtain ⟨B, hB, -⟩ := hP.2.2 (Classical.arbitrary U)
      exact Finset.card_pos.2 ⟨B, hB⟩
    | succ i ih =>
      intro hi
      obtain ⟨hQ, hQP, hc⟩ := ih (by omega)
      have hst := hsteps ⟨i, by omega⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at hst
      obtain ⟨S, -, hne, hQ'⟩ := hst
      rw [hQ']
      refine ⟨pt06_split_partition E S _ hQ,
        pt06_refines_trans (pt06_split_refines E S _) hQP, ?_⟩
      have := pt06_card_lt_split E _ S hQ hne
      omega
  obtain ⟨hQK, hQKP, hcK⟩ := key K (Nat.lt_succ_self K)
  have hlast : Qs (Fin.last K) = Qs ⟨K, Nat.lt_succ_self K⟩ := rfl
  rw [hlast]
  have hii : (¬ ∃ Q', NaiveStep E (Qs ⟨K, Nat.lt_succ_self K⟩) Q') →
      IsCoarsestStableRefinement E P (Qs ⟨K, Nat.lt_succ_self K⟩) := by
    intro hno
    have hstab : Stable E (Qs ⟨K, Nat.lt_succ_self K⟩) := by
      intro S hS
      by_contra hns
      apply hno
      refine ⟨split E S (Qs ⟨K, Nat.lt_succ_self K⟩), S, ⟨{S}, by simpa using hS, by simp⟩,
        fun heq => hns (pt06_stable_of_split_eq E _ S hQK heq), rfl⟩
    refine ⟨hQK, hQKP, hstab, ?_⟩
    intro R hR hRP hRs
    exact pt06_lemma2 E P hP K Qs hrun' R hR hRP hRs ⟨K, Nat.lt_succ_self K⟩
  refine ⟨le_trans hcK (pt06_card_le hQK), hii, ?_, ?_⟩
  · intro hnot
    by_contra hno
    exact hnot (hii hno)
  · intro Q₁ Q₂ h₁ h₂
    have h12 : Refines Q₁ Q₂ := h₂.2.2.2 Q₁ h₁.1 h₁.2.1 h₁.2.2.1
    have h21 : Refines Q₂ Q₁ := h₁.2.2.2 Q₂ h₂.1 h₂.2.1 h₂.2.2.1
    exact Finset.Subset.antisymm (pt06_partition_eq h₁.1 h₂.1 h12 h21)
      (pt06_partition_eq h₂.1 h₁.1 h21 h12)
