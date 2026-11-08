-- Prove2me | solution 1 for SteinerCutDominants.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:07:27.754545+00:00
-- url     : https://prove2.me/submissions/a2b8f37f-4690-4184-8825-f846acb1d6df

import Mathlib
import Definitions.Def_SteinerCutDominants_IsLaminar
import Definitions.Def_SteinerCutDominants_lminOf

namespace Aux_SCD_l1
open SteinerCutDominants

variable {V : Type} [DecidableEq V]

def Good (L : Finset (Finset V)) : Prop :=
  L.Nonempty → L.card + 1 ≤ (L.biUnion id).card + (lminOf L).card

lemma laminar_sub {L M : Finset (Finset V)} (h : M ⊆ L) (hL : IsLaminar L) : IsLaminar M :=
  fun A hA B hB => hL A (h hA) B (h hB)

lemma disj_of_not_sub (L : Finset (Finset V)) (hL : IsLaminar L) (R : Finset V) (hR : R ∈ L)
    (hmax : ∀ A ∈ L, A.card ≤ R.card) (A : Finset V) (hA : A ∈ L) (hAR : ¬ A ⊆ R) :
    Disjoint A R := by
  have hI := hL A hA R hR
  unfold Intersect at hI
  rw [Finset.disjoint_iff_inter_eq_empty]
  by_contra hne
  apply hI
  refine ⟨Finset.nonempty_iff_ne_empty.2 hne, ?_, ?_⟩
  · obtain ⟨x, hx, hxR⟩ := Finset.not_subset.1 hAR
    exact ⟨x, Finset.mem_sdiff.2 ⟨hx, hxR⟩⟩
  · by_contra hem
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hem
    have := Finset.eq_of_subset_of_card_le hem (hmax A hA)
    exact hAR (this ▸ le_refl _)

lemma split_bound (L : Finset (Finset V)) (hL : IsLaminar L) (hne : ∅ ∉ L)
    (R : Finset V) (hR : R ∈ L) (hmax : ∀ A ∈ L, A.card ≤ R.card)
    (hout : (L.filter (fun A => ¬ A ⊆ R)).Nonempty)
    (ih1 : Good (L.filter (fun A => A ⊆ R))) (ih2 : Good (L.filter (fun A => ¬ A ⊆ R))) :
    L.card + 2 ≤ (L.biUnion id).card + (lminOf L).card := by
  set Lin := L.filter (fun A => A ⊆ R) with hLin
  set Lout := L.filter (fun A => ¬ A ⊆ R) with hLout
  have h1 := ih1 ⟨R, Finset.mem_filter.2 ⟨hR, le_refl _⟩⟩
  have h2 := ih2 hout
  have hcard : L.card = Lin.card + Lout.card :=
    (Finset.card_filter_add_card_filter_not _).symm
  have hdisjout : ∀ A ∈ Lout, Disjoint A R := by
    intro A hA
    rw [hLout, Finset.mem_filter] at hA
    exact disj_of_not_sub L hL R hR hmax A hA.1 hA.2
  have hU : (L.biUnion id).card = (Lin.biUnion id).card + (Lout.biUnion id).card := by
    have e : L.biUnion id = Lin.biUnion id ∪ Lout.biUnion id := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_union, id, hLin, hLout, Finset.mem_filter]
      constructor
      · rintro ⟨A, hA, hx⟩
        by_cases h : A ⊆ R
        · exact Or.inl ⟨A, ⟨hA, h⟩, hx⟩
        · exact Or.inr ⟨A, ⟨hA, h⟩, hx⟩
      · rintro (⟨A, ⟨hA, _⟩, hx⟩ | ⟨A, ⟨hA, _⟩, hx⟩) <;> exact ⟨A, hA, hx⟩
    rw [e, Finset.card_union_of_disjoint]
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.1 hx1
    obtain ⟨B, hB, hxB⟩ := Finset.mem_biUnion.1 hx2
    have hA' : A ∈ L.filter (fun A => A ⊆ R) := by rw [← hLin]; exact hA
    have hAR : A ⊆ R := (Finset.mem_filter.1 hA').2
    exact Finset.disjoint_left.1 (hdisjout B hB) hxB (hAR hxA)
  have hmin : (lminOf L).card = (lminOf Lin).card + (lminOf Lout).card := by
    have e1 : lminOf Lin = (lminOf L).filter (fun A => A ⊆ R) := by
      ext A
      simp only [lminOf, Finset.mem_filter, hLin]
      constructor
      · rintro ⟨⟨hA, hAR⟩, hmin⟩
        refine ⟨⟨hA, fun B hB hBA => hmin B ⟨hB, hBA.trans hAR⟩ hBA⟩, hAR⟩
      · rintro ⟨⟨hA, hmin⟩, hAR⟩
        exact ⟨⟨hA, hAR⟩, fun B hB hBA => hmin B hB.1 hBA⟩
    have e2 : lminOf Lout = (lminOf L).filter (fun A => ¬ A ⊆ R) := by
      ext A
      simp only [lminOf, Finset.mem_filter, hLout]
      constructor
      · rintro ⟨⟨hA, hAR⟩, hmin⟩
        refine ⟨⟨hA, fun B hB hBA => ?_⟩, hAR⟩
        by_cases hBR : B ⊆ R
        · exfalso
          have hd := disj_of_not_sub L hL R hR hmax A hA hAR
          have : B = ∅ := by
            rw [← Finset.subset_empty]
            intro x hx
            exact absurd (hBR hx) (Finset.disjoint_left.1 hd (hBA hx))
          exact hne (this ▸ hB)
        · exact hmin B ⟨hB, hBR⟩ hBA
      · rintro ⟨⟨hA, hmin⟩, hAR⟩
        exact ⟨⟨hA, hAR⟩, fun B hB hBA => hmin B hB.1 hBA⟩
    rw [e1, e2]
    exact (Finset.card_filter_add_card_filter_not _).symm
  omega

lemma good_all (L : Finset (Finset V)) (hL : IsLaminar L) (hne : ∅ ∉ L) : Good L := by
  induction L using Finset.strongInduction with
  | H L ih =>
  intro hLne
  obtain ⟨R, hR, hmax⟩ := Finset.exists_max_image L Finset.card hLne
  have goodsub : ∀ M ⊂ L, Good M := fun M hM =>
    ih M hM (laminar_sub hM.subset hL) (fun h => hne (hM.subset h))
  by_cases hout : (L.filter (fun A => ¬ A ⊆ R)).Nonempty
  · have hR' : R ∈ L.filter (fun A => A ⊆ R) := Finset.mem_filter.2 ⟨hR, le_refl _⟩
    have := split_bound L hL hne R hR hmax hout
      (goodsub _ (Finset.filter_ssubset.2 (by
        obtain ⟨A, hA⟩ := hout
        exact ⟨A, (Finset.mem_filter.1 hA).1, (Finset.mem_filter.1 hA).2⟩)))
      (goodsub _ (Finset.filter_ssubset.2 ⟨R, hR, not_not.2 (le_refl _)⟩))
    omega
  · have hall : ∀ A ∈ L, A ⊆ R := by
      intro A hA
      by_contra h
      exact hout ⟨A, Finset.mem_filter.2 ⟨hA, h⟩⟩
    have hUR : L.biUnion id = R := by
      apply le_antisymm
      · intro x hx
        obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.1 hx
        exact hall A hA hxA
      · intro x hx
        exact Finset.mem_biUnion.2 ⟨R, hR, hx⟩
    set L2 := L.erase R with hL2
    have hL2sub : L2 ⊂ L := Finset.erase_ssubset hR
    have hRne : R.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h; exact hne (h ▸ hR)
    by_cases hL2ne : L2.Nonempty
    · have hminEq : lminOf L = lminOf L2 := by
        ext A
        simp only [lminOf, Finset.mem_filter, hL2, Finset.mem_erase]
        constructor
        · rintro ⟨hA, hmin⟩
          have hAR : A ≠ R := by
            rintro rfl
            obtain ⟨B, hB⟩ := hL2ne
            rw [hL2, Finset.mem_erase] at hB
            exact hB.1 (hmin B hB.2 (hall B hB.2))
          exact ⟨⟨hAR, hA⟩, fun B hB hBA => hmin B hB.2 hBA⟩
        · rintro ⟨⟨hAR, hA⟩, hmin⟩
          refine ⟨hA, fun B hB hBA => ?_⟩
          by_cases hBR : B = R
          · exfalso
            rw [hBR] at hBA
            exact hAR (le_antisymm (hall A hA) hBA)
          · exact hmin B ⟨hBR, hB⟩ hBA
      have hcard : L.card = L2.card + 1 := (Finset.card_erase_add_one hR).symm
      have hU2sub : L2.biUnion id ⊆ R := by
        intro x hx
        obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.1 hx
        exact hall A (Finset.mem_of_mem_erase hA) hxA
      rw [hUR, hminEq, hcard]
      rcases lt_or_eq_of_le (Finset.card_le_card hU2sub) with hlt | heq
      · have := goodsub L2 hL2sub hL2ne
        omega
      · -- the union of L2 is all of R: split L2
        have hU2 : L2.biUnion id = R := Finset.eq_of_subset_of_card_le hU2sub (le_of_eq heq.symm)
        obtain ⟨R1, hR1, hmax1⟩ := Finset.exists_max_image L2 Finset.card hL2ne
        have hL2lam : IsLaminar L2 := laminar_sub hL2sub.subset hL
        have hne2 : ∅ ∉ L2 := fun h => hne (hL2sub.subset h)
        have hout2 : (L2.filter (fun A => ¬ A ⊆ R1)).Nonempty := by
          by_contra hno
          have hall1 : ∀ A ∈ L2, A ⊆ R1 := by
            intro A hA
            by_contra h
            exact hno ⟨A, Finset.mem_filter.2 ⟨hA, h⟩⟩
          have : R ⊆ R1 := by
            rw [← hU2]
            intro x hx
            obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.1 hx
            exact hall1 A hA hxA
          have hR1R : R1 = R := le_antisymm (hall R1 (Finset.mem_of_mem_erase hR1)) this
          rw [hL2, Finset.mem_erase] at hR1
          exact hR1.1 hR1R
        have := split_bound L2 hL2lam hne2 R1 hR1 hmax1 hout2
          (goodsub _ (lt_of_le_of_lt (Finset.filter_subset _ _) hL2sub))
          (goodsub _ (lt_of_le_of_lt (Finset.filter_subset _ _) hL2sub))
        rw [hU2] at this
        omega
    · have hL1 : L = {R} := by
        rw [Finset.not_nonempty_iff_eq_empty, hL2] at hL2ne
        ext A
        constructor
        · intro hA
          by_contra h
          have : A ∈ L.erase R := Finset.mem_erase.2 ⟨fun e => h (Finset.mem_singleton.2 e), hA⟩
          rw [hL2ne] at this
          exact Finset.notMem_empty _ this
        · intro hA; rw [Finset.mem_singleton.1 hA]; exact hR
      have hmin1 : lminOf L = {R} := by
        rw [hL1]; ext A
        simp only [lminOf, Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨h, _⟩; exact h
        · rintro rfl; exact ⟨rfl, fun B hB _ => hB⟩
      rw [hUR, hmin1, hL1, Finset.card_singleton]
      have := Finset.card_pos.2 hRne
      omega

end Aux_SCD_l1

open SteinerCutDominants Aux_SCD_l1 in
theorem solution {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (L : Finset (Finset V))
    (hL : IsLaminar L) (hne : ∅ ∉ L) :
    L.card + 1 ≤ Fintype.card V + (lminOf L).card := by
  by_cases hLne : L.Nonempty
  · have h := good_all L hL hne hLne
    have : (L.biUnion id).card ≤ Fintype.card V := Finset.card_le_univ _
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hLne
    subst hLne
    have := Fintype.card_pos (α := V)
    simp
    omega
