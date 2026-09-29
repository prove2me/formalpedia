-- Prove2me | solution 1 for PaigeTarjan.Coarsest.improved_refinement_correct
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T10:56:19.490807+00:00
-- url     : https://prove2.me/submissions/1252c24d-193f-48cd-88b0-bc963ce61011

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic
import Definitions.Def_PaigeTarjan_Coarsest_Algorithms

set_option autoImplicit false

/-! ## Basic facts about preimages, partitions and `split` -/

open PaigeTarjan.Coarsest in
theorem pt4c_mem_preimage {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (x : U) :
    x ∈ preimage E T ↔ ∃ y ∈ T, E x y := by
  simp [preimage]

open PaigeTarjan.Coarsest in
theorem pt4c_part_eq {U : Type*} [Fintype U] [DecidableEq U]
    {X : Finset (Finset U)} (hX : IsPartition X) {A C : Finset U} (hA : A ∈ X) (hC : C ∈ X)
    {x : U} (hxA : x ∈ A) (hxC : x ∈ C) : A = C := by
  by_contra h
  exact Finset.disjoint_left.1 (hX.2.1 A hA C hC h) hxA hxC

open PaigeTarjan.Coarsest in
theorem pt4c_mem_split {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U))
    (C : Finset U) :
    C ∈ split E T Q ↔
      ∃ A ∈ Q, (C = A ∩ preimage E T ∨ C = A \ preimage E T) ∧ C.Nonempty := by
  simp only [split, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton]

open PaigeTarjan.Coarsest in
theorem pt4c_split_sub {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U))
    {C : Finset U} (hC : C ∈ split E T Q) : ∃ A ∈ Q, C ⊆ A := by
  obtain ⟨A, hA, h, -⟩ := (pt4c_mem_split E T Q C).1 hC
  refine ⟨A, hA, ?_⟩
  rcases h with rfl | rfl
  · exact Finset.inter_subset_left
  · exact Finset.sdiff_subset

open PaigeTarjan.Coarsest in
theorem pt4c_split_refines {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U)) :
    Refines (split E T Q) Q :=
  fun _ hC => pt4c_split_sub E T Q hC

open PaigeTarjan.Coarsest in
theorem pt4c_split_partition {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U))
    (hQ : IsPartition Q) : IsPartition (split E T Q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨A, -, -, hne⟩ := (pt4c_mem_split E T Q C).1 hC
    exact hne
  · intro C hC D hD hCD
    obtain ⟨A, hA, hCA, -⟩ := (pt4c_mem_split E T Q C).1 hC
    obtain ⟨A', hA', hDA, -⟩ := (pt4c_mem_split E T Q D).1 hD
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
    · refine ⟨A ∩ preimage E T, (pt4c_mem_split E T Q _).2
        ⟨A, hA, Or.inl rfl, ⟨x, Finset.mem_inter.2 ⟨hx, hp⟩⟩⟩, Finset.mem_inter.2 ⟨hx, hp⟩⟩
    · refine ⟨A \ preimage E T, (pt4c_mem_split E T Q _).2
        ⟨A, hA, Or.inr rfl, ⟨x, Finset.mem_sdiff.2 ⟨hx, hp⟩⟩⟩, Finset.mem_sdiff.2 ⟨hx, hp⟩⟩

open PaigeTarjan.Coarsest in
theorem pt4c_split_stable {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U)) :
    StableWrt E (split E T Q) T := by
  intro C hC
  obtain ⟨A, -, h, -⟩ := (pt4c_mem_split E T Q C).1 hC
  unfold StableBlock
  rcases h with rfl | rfl
  · left; exact Finset.inter_subset_right
  · right
    rw [Finset.disjoint_left]
    intro x hx
    exact (Finset.mem_sdiff.1 hx).2

open PaigeTarjan.Coarsest in
theorem pt4c_stable_mono {U : Type*} [Fintype U] [DecidableEq U]
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
theorem pt4c_refines_trans {U : Type*} [Fintype U] [DecidableEq U]
    {R Q P : Finset (Finset U)} (h1 : Refines R Q) (h2 : Refines Q P) : Refines R P := by
  intro D hD
  obtain ⟨A, hA, hDA⟩ := h1 D hD
  obtain ⟨C, hC, hAC⟩ := h2 A hA
  exact ⟨C, hC, hDA.trans hAC⟩

open PaigeTarjan.Coarsest in
theorem pt4c_refines_split {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] {R Q : Finset (Finset U)} {T : Finset U}
    (hR : IsPartition R) (hRQ : Refines R Q) (hs : StableWrt E R T) :
    Refines R (split E T Q) := by
  intro D hD
  obtain ⟨A, hA, hDA⟩ := hRQ D hD
  obtain ⟨x, hx⟩ := hR.1 D hD
  have hsD := hs D hD
  unfold StableBlock at hsD
  rcases hsD with h | h
  · refine ⟨A ∩ preimage E T, (pt4c_mem_split E T Q _).2
      ⟨A, hA, Or.inl rfl, ⟨x, Finset.mem_inter.2 ⟨hDA hx, h hx⟩⟩⟩, ?_⟩
    exact Finset.subset_inter hDA h
  · refine ⟨A \ preimage E T, (pt4c_mem_split E T Q _).2
      ⟨A, hA, Or.inr rfl, ⟨x, Finset.mem_sdiff.2 ⟨hDA hx, Finset.disjoint_left.1 h hx⟩⟩⟩, ?_⟩
    intro y hy
    exact Finset.mem_sdiff.2 ⟨hDA hy, Finset.disjoint_left.1 h hy⟩

open PaigeTarjan.Coarsest in
theorem pt4c_stable_of_sat {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] {R : Finset (Finset U)} {T : Finset U}
    (hR : IsPartition R) (hst : Stable E R) (hsat : ∀ D ∈ R, D ⊆ T ∨ Disjoint D T) :
    StableWrt E R T := by
  intro D hD
  unfold StableBlock
  by_cases hex : ∃ x ∈ D, x ∈ preimage E T
  · obtain ⟨x, hxD, hxp⟩ := hex
    obtain ⟨y, hyT, hxy⟩ := (pt4c_mem_preimage E T x).1 hxp
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
      obtain ⟨w, hw, hzw⟩ := (pt4c_mem_preimage E D' z).1 (h hz)
      exact (pt4c_mem_preimage E T z).2 ⟨w, hD'T hw, hzw⟩
    · exact absurd ((pt4c_mem_preimage E D' x).2 ⟨y, hyD', hxy⟩) (Finset.disjoint_left.1 h hxD)
  · right
    rw [Finset.disjoint_left]
    intro x hx hxp
    exact hex ⟨x, hx, hxp⟩

open PaigeTarjan.Coarsest in
theorem pt4c_card_le {U : Type*} [Fintype U] [DecidableEq U]
    {X : Finset (Finset U)} (hX : IsPartition X) : X.card ≤ Fintype.card U := by
  have hdisj : (X : Set (Finset U)).PairwiseDisjoint id := by
    intro A hA B hB h
    exact hX.2.1 A hA B hB h
  calc X.card = ∑ _T ∈ X, 1 := by simp
    _ ≤ ∑ T ∈ X, T.card := Finset.sum_le_sum (fun T hT => Finset.card_pos.2 (hX.1 T hT))
    _ = (X.biUnion id).card := (Finset.card_biUnion hdisj).symm
    _ ≤ Fintype.card U := Finset.card_le_univ _

/-! ## One step of the improved algorithm -/

theorem pt4c_mem_newX {U : Type*} [DecidableEq U] {X : Finset (Finset U)} {S B T : Finset U} :
    T ∈ insert B (insert (S \ B) (X.erase S)) ↔ T = B ∨ T = S \ B ∨ (T ≠ S ∧ T ∈ X) := by
  simp only [Finset.mem_insert, Finset.mem_erase]

open PaigeTarjan.Coarsest in
theorem pt4c_step {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] {Q X Q' X' : Finset (Finset U)} {S B : Finset U}
    (hQ : IsPartition Q) (hX : IsPartition X) (hQX : Refines Q X)
    (hstab : ∀ T ∈ X, StableWrt E Q T)
    (hst : ImprovedStep E Q X S B Q' X') :
    IsPartition Q' ∧ IsPartition X' ∧ Refines Q' X' ∧ (∀ T ∈ X', StableWrt E Q' T) ∧
      Refines Q' Q ∧ X'.card = X.card + 1 ∧
      (∀ R : Finset (Finset U), IsPartition R → Stable E R → Refines R Q → Refines R Q') ∧
      (∀ (z : U) (T : Finset U), T ∈ X → z ∈ T →
        ∃ T' ∈ X', z ∈ T' ∧ T'.card ≤ T.card ∧ (z ∈ B → 2 * T'.card ≤ T.card)) := by
  obtain ⟨hSX, hSQ, hBQ, hBS, hcard, rfl, rfl⟩ := hst
  have hBne : B.Nonempty := hQ.1 B hBQ
  have hSBne : (S \ B).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [Finset.sdiff_eq_empty_iff_subset] at h
    have hBSeq : B = S := Finset.Subset.antisymm hBS h
    have := Finset.card_pos.2 hBne
    rw [hBSeq] at hcard this
    omega
  -- X' is a partition
  have hX'eq : ∀ T1 ∈ insert B (insert (S \ B) (X.erase S)),
      ∀ T2 ∈ insert B (insert (S \ B) (X.erase S)), ∀ z : U, z ∈ T1 → z ∈ T2 → T1 = T2 := by
    intro T1 h1 T2 h2 z hz1 hz2
    rw [pt4c_mem_newX] at h1 h2
    rcases h1 with rfl | rfl | ⟨h1S, h1X⟩ <;> rcases h2 with rfl | rfl | ⟨h2S, h2X⟩
    · rfl
    · exact absurd hz1 (Finset.mem_sdiff.1 hz2).2
    · exact absurd (pt4c_part_eq hX h2X hSX hz2 (hBS hz1)) h2S
    · exact absurd hz2 (Finset.mem_sdiff.1 hz1).2
    · rfl
    · exact absurd (pt4c_part_eq hX h2X hSX hz2 (Finset.mem_sdiff.1 hz1).1) h2S
    · exact absurd (pt4c_part_eq hX h1X hSX hz1 (hBS hz2)) h1S
    · exact absurd (pt4c_part_eq hX h1X hSX hz1 (Finset.mem_sdiff.1 hz2).1) h1S
    · exact pt4c_part_eq hX h1X h2X hz1 hz2
  have hX' : IsPartition (insert B (insert (S \ B) (X.erase S))) := by
    refine ⟨?_, ?_, ?_⟩
    · intro T hT
      rw [pt4c_mem_newX] at hT
      rcases hT with rfl | rfl | ⟨-, hT⟩
      · exact hBne
      · exact hSBne
      · exact hX.1 T hT
    · intro T1 h1 T2 h2 hne
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      exact hne (hX'eq T1 h1 T2 h2 z hz1 hz2)
    · intro z
      obtain ⟨T, hT, hz⟩ := hX.2.2 z
      by_cases hTS : T = S
      · subst hTS
        by_cases hzB : z ∈ B
        · exact ⟨B, pt4c_mem_newX.2 (Or.inl rfl), hzB⟩
        · exact ⟨T \ B, pt4c_mem_newX.2 (Or.inr (Or.inl rfl)), Finset.mem_sdiff.2 ⟨hz, hzB⟩⟩
      · exact ⟨T, pt4c_mem_newX.2 (Or.inr (Or.inr ⟨hTS, hT⟩)), hz⟩
  have hQ'Q : Refines (split E (S \ B) (split E B Q)) Q :=
    pt4c_refines_trans (pt4c_split_refines E _ _) (pt4c_split_refines E _ _)
  have hQX' : Refines Q (insert B (insert (S \ B) (X.erase S))) := by
    intro A hA
    obtain ⟨T, hT, hAT⟩ := hQX A hA
    by_cases hTS : T = S
    · subst hTS
      by_cases hAB : A = B
      · subst hAB
        exact ⟨A, pt4c_mem_newX.2 (Or.inl rfl), subset_rfl⟩
      · refine ⟨T \ B, pt4c_mem_newX.2 (Or.inr (Or.inl rfl)), ?_⟩
        intro z hz
        exact Finset.mem_sdiff.2 ⟨hAT hz, fun hzB => hAB (pt4c_part_eq hQ hA hBQ hz hzB)⟩
    · exact ⟨T, pt4c_mem_newX.2 (Or.inr (Or.inr ⟨hTS, hT⟩)), hAT⟩
  refine ⟨pt4c_split_partition E _ _ (pt4c_split_partition E _ _ hQ), hX',
    pt4c_refines_trans hQ'Q hQX', ?_, hQ'Q, ?_, ?_, ?_⟩
  · -- stability
    intro T hT
    rw [pt4c_mem_newX] at hT
    rcases hT with rfl | rfl | ⟨-, hT⟩
    · exact pt4c_stable_mono E (pt4c_split_refines E _ _) (pt4c_split_stable E _ _)
    · exact pt4c_split_stable E _ _
    · exact pt4c_stable_mono E hQ'Q (hstab T hT)
  · -- card
    have hB1 : B ∉ insert (S \ B) (X.erase S) := by
      intro h
      obtain ⟨z, hz⟩ := hBne
      rw [Finset.mem_insert, Finset.mem_erase] at h
      rcases h with h | ⟨hBS', hBX⟩
      · have := hz
        rw [h] at this
        exact (Finset.mem_sdiff.1 this).2 hz
      · exact hBS' (pt4c_part_eq hX hBX hSX hz (hBS hz))
    have hB2 : S \ B ∉ X.erase S := by
      intro h
      obtain ⟨z, hz⟩ := hSBne
      rw [Finset.mem_erase] at h
      exact h.1 (pt4c_part_eq hX h.2 hSX hz (Finset.mem_sdiff.1 hz).1)
    rw [Finset.card_insert_of_notMem hB1, Finset.card_insert_of_notMem hB2,
      Finset.card_erase_of_mem hSX]
    have := Finset.card_pos.2 ⟨S, hSX⟩
    omega
  · -- coarsest preservation
    intro R hR hRst hRQ
    have satB : ∀ D ∈ R, D ⊆ B ∨ Disjoint D B := by
      intro D hD
      obtain ⟨A, hA, hDA⟩ := hRQ D hD
      by_cases hAB : A = B
      · subst hAB; left; exact hDA
      · right; exact (hQ.2.1 A hA B hBQ hAB).mono_left hDA
    have satSB : ∀ D ∈ R, D ⊆ S \ B ∨ Disjoint D (S \ B) := by
      intro D hD
      obtain ⟨A, hA, hDA⟩ := hRQ D hD
      obtain ⟨T, hT, hAT⟩ := hQX A hA
      rcases satB D hD with h | h
      · right
        rw [Finset.disjoint_left]
        intro z hz hz'
        exact (Finset.mem_sdiff.1 hz').2 (h hz)
      · by_cases hTS : T = S
        · subst hTS
          left
          intro z hz
          exact Finset.mem_sdiff.2 ⟨hAT (hDA hz), Finset.disjoint_left.1 h hz⟩
        · right
          exact (hX.2.1 T hT S hSX hTS).mono (hDA.trans hAT) Finset.sdiff_subset
    have r1 : Refines R (split E B Q) :=
      pt4c_refines_split E hR hRQ (pt4c_stable_of_sat E hR hRst satB)
    exact pt4c_refines_split E hR r1 (pt4c_stable_of_sat E hR hRst satSB)
  · -- block tracking
    intro z T hT hz
    by_cases hTS : T = S
    · subst hTS
      by_cases hzB : z ∈ B
      · exact ⟨B, pt4c_mem_newX.2 (Or.inl rfl), hzB, Finset.card_le_card hBS, fun _ => hcard⟩
      · exact ⟨T \ B, pt4c_mem_newX.2 (Or.inr (Or.inl rfl)), Finset.mem_sdiff.2 ⟨hz, hzB⟩,
          Finset.card_le_card Finset.sdiff_subset, fun h => absurd h hzB⟩
    · exact ⟨T, pt4c_mem_newX.2 (Or.inr (Or.inr ⟨hTS, hT⟩)), hz, le_rfl,
        fun hzB => absurd (pt4c_part_eq hX hT hSX hz (hBS hzB)) hTS⟩

/-! ## Progress: if `Q ≠ X` a further step applies -/

open PaigeTarjan.Coarsest in
theorem pt4c_progress {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] {Q X : Finset (Finset U)}
    (hQ : IsPartition Q) (hX : IsPartition X) (hQX : Refines Q X) (hne : Q ≠ X) :
    ∃ (S B : Finset U) (Q' X' : Finset (Finset U)), ImprovedStep E Q X S B Q' X' := by
  have hex : ∃ S ∈ X, S ∉ Q := by
    by_contra hcon
    push Not at hcon
    apply hne
    ext C
    constructor
    · intro hC
      obtain ⟨x, hx⟩ := hQ.1 C hC
      obtain ⟨T, hT, hCT⟩ := hQX C hC
      have hTQ := hcon T hT
      rw [pt4c_part_eq hQ hC hTQ hx (hCT hx)]
      exact hT
    · intro hC
      exact hcon C hC
  obtain ⟨S, hSX, hSQ⟩ := hex
  -- every Q-block meeting S lies in S
  have hin : ∀ A ∈ Q, ∀ x ∈ A, x ∈ S → A ⊆ S := by
    intro A hA x hxA hxS
    obtain ⟨T, hT, hAT⟩ := hQX A hA
    rw [← pt4c_part_eq hX hT hSX (hAT hxA) hxS]
    exact hAT
  obtain ⟨x, hxS⟩ := hX.1 S hSX
  obtain ⟨A, hA, hxA⟩ := hQ.2.2 x
  have hAS := hin A hA x hxA hxS
  have hy : ∃ y ∈ S, y ∉ A := by
    by_contra hcon
    push Not at hcon
    have : A = S := Finset.Subset.antisymm hAS hcon
    exact hSQ (this ▸ hA)
  obtain ⟨y, hyS, hyA⟩ := hy
  obtain ⟨A', hA', hyA'⟩ := hQ.2.2 y
  have hA'S := hin A' hA' y hyA' hyS
  have hAA' : A ≠ A' := by
    intro h
    exact hyA (h ▸ hyA')
  have hdisj := hQ.2.1 A hA A' hA' hAA'
  have hsum : A.card + A'.card ≤ S.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.union_subset hAS hA'S)
  by_cases h2 : 2 * A.card ≤ S.card
  · exact ⟨S, A, _, _, hSX, hSQ, hA, hAS, h2, rfl, rfl⟩
  · exact ⟨S, A', _, _, hSX, hSQ, hA', hA'S, by omega, rfl, rfl⟩

/-! ## Runs indexed by `ℕ` -/

open PaigeTarjan.Coarsest in
theorem pt4c_run {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    (E : U → U → Prop) [DecidableRel E] (hE : ∀ x : U, ∃ y : U, E x y)
    (P : Finset (Finset U)) (hP : IsPartition P) (K : ℕ)
    (q xs : ℕ → Finset (Finset U)) (s b : ℕ → Finset U)
    (h0q : q 0 = P) (h0x : xs 0 = {Finset.univ})
    (hstep : ∀ i, i < K → ImprovedStep E (q i) (xs i) (s i) (b i) (q (i + 1)) (xs (i + 1))) :
    ∀ i, i ≤ K →
      IsPartition (q i) ∧ IsPartition (xs i) ∧ Refines (q i) (xs i) ∧
      (∀ T ∈ xs i, StableWrt E (q i) T) ∧ Refines (q i) P ∧
      (∀ R : Finset (Finset U), IsPartition R → Stable E R → Refines R P → Refines R (q i)) ∧
      (xs i).card = i + 1 ∧
      ∀ z : U, ∃ T ∈ xs i, z ∈ T ∧
        T.card * 2 ^ ((Finset.range i).filter (fun j => z ∈ b j)).card ≤ Fintype.card U := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [h0q, h0x]
    refine ⟨hP, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro B hB
        rw [Finset.mem_singleton.1 hB]
        exact Finset.univ_nonempty
      · intro B hB C hC h
        exact absurd ((Finset.mem_singleton.1 hB).trans (Finset.mem_singleton.1 hC).symm) h
      · intro x
        exact ⟨Finset.univ, Finset.mem_singleton_self _, Finset.mem_univ x⟩
    · intro B _
      exact ⟨Finset.univ, Finset.mem_singleton_self _, Finset.subset_univ B⟩
    · intro T hT A _
      rw [Finset.mem_singleton.1 hT]
      unfold StableBlock
      left
      intro x _
      obtain ⟨y, hy⟩ := hE x
      exact (pt4c_mem_preimage E _ x).2 ⟨y, Finset.mem_univ y, hy⟩
    · intro B hB
      exact ⟨B, hB, subset_rfl⟩
    · intro R _ _ hR
      exact hR
    · simp
    · intro z
      refine ⟨Finset.univ, Finset.mem_singleton_self _, Finset.mem_univ z, ?_⟩
      simp
  | succ i ih =>
    intro hi
    obtain ⟨hQ, hX, hQX, hstab, hQP, hcoarse, hcard, htrack⟩ := ih (by omega)
    obtain ⟨hQ', hX', hQX', hstab', hQ'Q, hcard', hcoarse', htrack'⟩ :=
      pt4c_step E hQ hX hQX hstab (hstep i (by omega))
    refine ⟨hQ', hX', hQX', hstab', pt4c_refines_trans hQ'Q hQP, ?_, by omega, ?_⟩
    · intro R hR hRst hRP
      exact hcoarse' R hR hRst (hcoarse R hR hRst hRP)
    · intro z
      obtain ⟨T, hT, hzT, hle⟩ := htrack z
      obtain ⟨T', hT', hzT', hT'le, hhalf⟩ := htrack' z T hT hzT
      refine ⟨T', hT', hzT', ?_⟩
      rw [Finset.range_add_one, Finset.filter_insert]
      by_cases hzb : z ∈ b i
      · rw [if_pos hzb, Finset.card_insert_of_notMem (by simp), pow_succ]
        have := hhalf hzb
        calc T'.card * (2 ^ ((Finset.range i).filter (fun j => z ∈ b j)).card * 2)
            = (2 * T'.card) * 2 ^ ((Finset.range i).filter (fun j => z ∈ b j)).card := by ring
          _ ≤ T.card * 2 ^ ((Finset.range i).filter (fun j => z ∈ b j)).card :=
            Nat.mul_le_mul_right _ this
          _ ≤ Fintype.card U := hle
      · rw [if_neg hzb]
        exact le_trans (Nat.mul_le_mul_right _ hT'le) hle

/-! ## The theorem -/

open PaigeTarjan.Coarsest in
theorem solution {U : Type*} [Fintype U] [DecidableEq U] [Nonempty U]
    (E : U → U → Prop) [DecidableRel E] (hE : ∀ x : U, ∃ y : U, E x y)
    (P : Finset (Finset U)) (hP : IsPartition P)
    (K : ℕ) (Qs Xs : Fin (K + 1) → Finset (Finset U)) (Ss Bs : Fin K → Finset U)
    (hrun : IsImprovedRun E P K Qs Xs Ss Bs) :
    (∀ j : Fin (K + 1), IsPartition (Qs j) ∧ IsPartition (Xs j) ∧
      Refines (Qs j) (Xs j) ∧ ∀ S ∈ Xs j, StableWrt E (Qs j) S) ∧
    (Qs (Fin.last K) = Xs (Fin.last K) →
      IsCoarsestStableRefinement E P (Qs (Fin.last K))) ∧
    (Qs (Fin.last K) ≠ Xs (Fin.last K) →
      ∃ (S B : Finset U) (Q' X' : Finset (Finset U)),
        ImprovedStep E (Qs (Fin.last K)) (Xs (Fin.last K)) S B Q' X') ∧
    K + 1 ≤ Fintype.card U ∧
    (∀ x : U, ((Finset.univ.filter (fun j : Fin K => x ∈ Bs j)).card : ℝ) ≤
      Real.logb 2 (Fintype.card U) + 1) := by
  obtain ⟨h0Q, h0X, hsteps⟩ := hrun
  obtain ⟨q, hq⟩ : ∃ q : ℕ → Finset (Finset U), ∀ j : Fin (K + 1), q j = Qs j :=
    ⟨fun i => if h : i < K + 1 then Qs ⟨i, h⟩ else ∅, fun j => by simp [j.isLt]⟩
  obtain ⟨xs, hx⟩ : ∃ xs : ℕ → Finset (Finset U), ∀ j : Fin (K + 1), xs j = Xs j :=
    ⟨fun i => if h : i < K + 1 then Xs ⟨i, h⟩ else ∅, fun j => by simp [j.isLt]⟩
  obtain ⟨s, hs⟩ : ∃ s : ℕ → Finset U, ∀ j : Fin K, s j = Ss j :=
    ⟨fun i => if h : i < K then Ss ⟨i, h⟩ else ∅, fun j => by simp [j.isLt]⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ → Finset U, ∀ j : Fin K, b j = Bs j :=
    ⟨fun i => if h : i < K then Bs ⟨i, h⟩ else ∅, fun j => by simp [j.isLt]⟩
  have key : ∀ i, i < K →
      ImprovedStep E (q i) (xs i) (s i) (b i) (q (i + 1)) (xs (i + 1)) := by
    intro i hi
    have h := hsteps ⟨i, hi⟩
    rw [← hq, ← hq, ← hx, ← hx, ← hs, ← hb] at h
    exact h
  have h0q : q 0 = P := by rw [← h0Q]; exact hq 0
  have h0x : xs 0 = {Finset.univ} := by rw [← h0X]; exact hx 0
  have run := pt4c_run E hE P hP K q xs s b h0q h0x key
  have hlastq : q K = Qs (Fin.last K) := hq (Fin.last K)
  have hlastx : xs K = Xs (Fin.last K) := hx (Fin.last K)
  obtain ⟨hQK, hXK, hQXK, hstabK, hQPK, hcoarseK, hcardK, htrackK⟩ := run K le_rfl
  rw [hlastq] at hQK hQXK hstabK hQPK hcoarseK
  rw [hlastx] at hXK hQXK hstabK hcardK
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    obtain ⟨h1, h2, h3, h4, -⟩ := run j (by omega)
    rw [hq j] at h1 h3 h4
    rw [hx j] at h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  · intro heq
    refine ⟨hQK, hQPK, ?_, fun R hR hRP hRst => hcoarseK R hR hRst hRP⟩
    intro S hS
    exact hstabK S (heq ▸ hS)
  · intro hne
    exact pt4c_progress E hQK hXK hQXK hne
  · rw [← hcardK]
    exact pt4c_card_le hXK
  · intro z
    obtain ⟨T, -, hzT, hle⟩ := htrackK z
    have hcnt : (Finset.univ.filter (fun j : Fin K => z ∈ Bs j)).card =
        ((Finset.range K).filter (fun j => z ∈ b j)).card := by
      rw [Finset.card_filter, Finset.card_filter,
        ← Fin.sum_univ_eq_sum_range (fun j => if z ∈ b j then 1 else 0)]
      simp only [hb]
    have hT1 : 1 ≤ T.card := Finset.card_pos.2 ⟨z, hzT⟩
    have h2 : 2 ^ ((Finset.range K).filter (fun j => z ∈ b j)).card ≤ Fintype.card U :=
      le_trans (Nat.le_mul_of_pos_left _ hT1) hle
    have hpos : (0 : ℝ) < (Fintype.card U : ℝ) := Nat.cast_pos.2 Fintype.card_pos
    have hreal : (2 : ℝ) ^ (((Finset.range K).filter (fun j => z ∈ b j)).card : ℝ)
        ≤ (Fintype.card U : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast h2
    have hlog := (Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) hpos).2 hreal
    rw [hcnt]
    linarith
