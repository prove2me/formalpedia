-- Prove2me | solution 1 for SoficGroups.KunTransportedAmbientOverlap.sum_intersection_boundary_le_partition_boundaries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/64a8f758-a444-44dd-81ab-dba4d7646a94

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_sum_intersection_generator_exit_card_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunTransportedAmbientOverlap
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.KunTransportedAmbientOverlap
theorem _root_.solution
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    {U : Finset V} (P Q : Finpartition U)
    (σ : ι → Equiv.Perm V) :
    (∑ C ∈ P.parts, ∑ D ∈ Q.parts,
      SoficGroups.boundary σ (C ∩ D)) ≤
      (∑ C ∈ P.parts, SoficGroups.boundary σ C) +
        (∑ D ∈ Q.parts, SoficGroups.boundary σ D) := by
  classical
  calc
    (∑ C ∈ P.parts, ∑ D ∈ Q.parts,
      SoficGroups.boundary σ (C ∩ D)) =
      ∑ i : ι, ∑ C ∈ P.parts, ∑ D ∈ Q.parts,
        ((C ∩ D).filter fun x => σ i x ∉ C ∩ D).card := by
      simp_rw [SoficGroups.boundary]
      calc
        (∑ C ∈ P.parts, ∑ D ∈ Q.parts, ∑ i : ι,
          ((C ∩ D).filter fun x => σ i x ∉ C ∩ D).card) =
            ∑ C ∈ P.parts, ∑ i : ι, ∑ D ∈ Q.parts,
              ((C ∩ D).filter fun x => σ i x ∉ C ∩ D).card := by
          apply Finset.sum_congr rfl
          intro C _
          rw [Finset.sum_comm]
        _ = ∑ i : ι, ∑ C ∈ P.parts, ∑ D ∈ Q.parts,
              ((C ∩ D).filter fun x => σ i x ∉ C ∩ D).card := by
          rw [Finset.sum_comm]
    _ ≤ ∑ i : ι,
      ((∑ C ∈ P.parts, (C.filter fun x => σ i x ∉ C).card) +
        (∑ D ∈ Q.parts, (D.filter fun x => σ i x ∉ D).card)) := by
      apply Finset.sum_le_sum
      intro i _
      exact sum_intersection_generator_exit_card_le P Q (σ i)
    _ = (∑ C ∈ P.parts, SoficGroups.boundary σ C) +
        (∑ D ∈ Q.parts, SoficGroups.boundary σ D) := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      · simp_rw [SoficGroups.boundary]
        rw [Finset.sum_comm]
      · simp_rw [SoficGroups.boundary]
        rw [Finset.sum_comm]
end SoficGroups.KunTransportedAmbientOverlap
