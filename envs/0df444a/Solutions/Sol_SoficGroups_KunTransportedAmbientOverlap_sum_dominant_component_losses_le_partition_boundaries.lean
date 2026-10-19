-- Prove2me | solution 1 for SoficGroups.KunTransportedAmbientOverlap.sum_dominant_component_losses_le_partition_boundaries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/49c95b1d-63c9-4f3d-8b76-890190298a01

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_sum_intersection_boundary_le_partition_boundaries
import Theorems.Thm_SoficGroups_KunTransportedAmbientOverlap_dominant_component_loss_le_ambient_intersection_boundaries

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
    (σ : ι → Equiv.Perm V) (gamma : ℝ)
    (hexp : ∀ C ∈ P.parts, ∀ E : Finset V, E ⊆ C →
      2 * E.card ≤ C.card →
        gamma * (E.card : ℝ) ≤
          (SoficGroups.boundary σ E : ℝ)) :
    gamma *
        (∑ C ∈ P.parts,
          ((C.card : ℝ) -
            ((C ∩ SoficGroups.maximumOverlapPart Q C).card : ℝ))) ≤
      (∑ C ∈ P.parts, (SoficGroups.boundary σ C : ℝ)) +
        (∑ D ∈ Q.parts, (SoficGroups.boundary σ D : ℝ)) := by
  classical
  calc
    gamma *
        (∑ C ∈ P.parts,
          ((C.card : ℝ) -
            ((C ∩ SoficGroups.maximumOverlapPart Q C).card : ℝ))) =
      ∑ C ∈ P.parts,
        gamma * ((C.card : ℝ) -
          ((C ∩ SoficGroups.maximumOverlapPart Q C).card : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ ∑ C ∈ P.parts, ∑ D ∈ Q.parts,
          (SoficGroups.boundary σ (C ∩ D) : ℝ) := by
        apply Finset.sum_le_sum
        intro C hC
        exact dominant_component_loss_le_ambient_intersection_boundaries
          P Q σ gamma hexp C hC
    _ ≤ (∑ C ∈ P.parts, (SoficGroups.boundary σ C : ℝ)) +
        (∑ D ∈ Q.parts, (SoficGroups.boundary σ D : ℝ)) := by
      exact_mod_cast
        sum_intersection_boundary_le_partition_boundaries P Q σ
end SoficGroups.KunTransportedAmbientOverlap
