-- Prove2me | solution 1 for SoficGroups.KunTransportedAmbientOverlap.sum_intersection_generator_exit_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/ed15ae91-3298-4337-96fa-79defa6022b2

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_sum_card_inter_partition
import Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_intersection_generator_exit_subset_union

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunTransportedAmbientOverlap
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunTransportedAmbientOverlap
theorem _root_.solution
    {V : Type*} [DecidableEq V]
    {U : Finset V} (P Q : Finpartition U)
    (p : Equiv.Perm V) :
    (∑ C ∈ P.parts, ∑ D ∈ Q.parts,
      ((C ∩ D).filter fun x => p x ∉ C ∩ D).card) ≤
      (∑ C ∈ P.parts,
        (C.filter fun x => p x ∉ C).card) +
      (∑ D ∈ Q.parts,
        (D.filter fun x => p x ∉ D).card) := by
  classical
  have hcell (C D : Finset V) :
      ((C ∩ D).filter fun x => p x ∉ C ∩ D).card ≤
        (((C.filter fun x => p x ∉ C) ∩ D).card) +
          (((D.filter fun x => p x ∉ D) ∩ C).card) :=
    (Finset.card_le_card
      (intersection_generator_exit_subset_union p C D)).trans
        (Finset.card_union_le _ _)
  have hfirst (C : Finset V) (hC : C ∈ P.parts) :
      (∑ D ∈ Q.parts,
        ((C.filter fun x => p x ∉ C) ∩ D).card) =
        (C.filter fun x => p x ∉ C).card := by
    have h := SoficGroups.sum_card_inter_partition Q
      (C.filter fun x => p x ∉ C)
    have hsub :
        (C.filter fun x => p x ∉ C) ⊆ U :=
      (Finset.filter_subset _ _).trans (P.subset hC)
    simpa [Finset.inter_comm,
      Finset.inter_eq_right.mpr hsub] using h
  have hsecond (D : Finset V) (hD : D ∈ Q.parts) :
      (∑ C ∈ P.parts,
        ((D.filter fun x => p x ∉ D) ∩ C).card) =
        (D.filter fun x => p x ∉ D).card := by
    have h := SoficGroups.sum_card_inter_partition P
      (D.filter fun x => p x ∉ D)
    have hsub :
        (D.filter fun x => p x ∉ D) ⊆ U :=
      (Finset.filter_subset _ _).trans (Q.subset hD)
    simpa [Finset.inter_comm,
      Finset.inter_eq_right.mpr hsub] using h
  calc
    (∑ C ∈ P.parts, ∑ D ∈ Q.parts,
      ((C ∩ D).filter fun x => p x ∉ C ∩ D).card) ≤
        ∑ C ∈ P.parts, ∑ D ∈ Q.parts,
          ((((C.filter fun x => p x ∉ C) ∩ D).card) +
            (((D.filter fun x => p x ∉ D) ∩ C).card)) := by
      apply Finset.sum_le_sum
      intro C _
      apply Finset.sum_le_sum
      intro D _
      exact hcell C D
    _ = (∑ C ∈ P.parts, ∑ D ∈ Q.parts,
          ((C.filter fun x => p x ∉ C) ∩ D).card) +
        (∑ D ∈ Q.parts, ∑ C ∈ P.parts,
          ((D.filter fun x => p x ∉ D) ∩ C).card) := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
    _ = (∑ C ∈ P.parts,
          (C.filter fun x => p x ∉ C).card) +
        (∑ D ∈ Q.parts,
          (D.filter fun x => p x ∉ D).card) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro C hC
        exact hfirst C hC
      · apply Finset.sum_congr rfl
        intro D hD
        exact hsecond D hD
end SoficGroups.KunTransportedAmbientOverlap
