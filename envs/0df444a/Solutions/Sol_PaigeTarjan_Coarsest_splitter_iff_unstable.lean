-- Prove2me | solution 1 for PaigeTarjan.Coarsest.splitter_iff_unstable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:45:56.947074+00:00
-- url     : https://prove2.me/submissions/e10ce64c-5522-4986-afa7-413e0976b78e

import Mathlib
import Definitions.Def_PaigeTarjan_Coarsest_Basic

set_option autoImplicit false

open PaigeTarjan.Coarsest in
theorem pt9e_mem_split {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (T : Finset U) (Q : Finset (Finset U))
    (C : Finset U) :
    C ∈ split E T Q ↔
      ∃ A ∈ Q, (C = A ∩ preimage E T ∨ C = A \ preimage E T) ∧ C.Nonempty := by
  simp only [split, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_singleton]

open PaigeTarjan.Coarsest in
theorem pt9e_split_stable {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (Q : Finset (Finset U)) (S : Finset U)
    (hQ : IsPartition Q) (hs : StableWrt E Q S) : split E S Q = Q := by
  ext C
  rw [pt9e_mem_split]
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
theorem solution {U : Type*} [Fintype U] [DecidableEq U]
    (E : U → U → Prop) [DecidableRel E] (Q : Finset (Finset U)) (S : Finset U)
    (hQ : IsPartition Q) :
    split E S Q ≠ Q ↔ ¬ StableWrt E Q S := by
  constructor
  · intro h hs
    exact h (pt9e_split_stable E Q S hQ hs)
  · intro hns heq
    apply hns
    intro B hB
    by_contra hBs
    unfold StableBlock at hBs
    push_neg at hBs
    obtain ⟨hsub, hndisj⟩ := hBs
    have hI : (B ∩ preimage E S).Nonempty := Finset.not_disjoint_iff_nonempty_inter.1 hndisj
    have hD : (B \ preimage E S).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, Ne, Finset.sdiff_eq_empty_iff_subset]
      exact hsub
    have hIQ : B ∩ preimage E S ∈ Q := by
      rw [← heq, pt9e_mem_split]
      exact ⟨B, hB, Or.inl rfl, hI⟩
    have hne : B ∩ preimage E S ≠ B := by
      intro h
      apply hsub
      rw [← h]
      exact Finset.inter_subset_right
    have hdis := hQ.2.1 _ hIQ B hB hne
    obtain ⟨x, hx⟩ := hI
    exact Finset.disjoint_left.1 hdis hx (Finset.mem_inter.1 hx).1
