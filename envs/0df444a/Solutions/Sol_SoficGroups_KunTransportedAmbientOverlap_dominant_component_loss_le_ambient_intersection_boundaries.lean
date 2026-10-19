-- Prove2me | solution 1 for SoficGroups.KunTransportedAmbientOverlap.dominant_component_loss_le_ambient_intersection_boundaries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/92adaef0-8582-41a3-95e7-a6a2791578b4

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_sum_card_component_inter_partition
import Theorems.Thm_SoficGroups_maximumOverlapPart_mem
import Theorems.Thm_SoficGroups_maximumOverlapPart_maximal
import Theorems.Thm_SoficGroups_KunRootedWordPower_RootedIndicatorMarkovModel_IsRootedAtRadius_mono

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
          (SoficGroups.boundary σ E : ℝ))
    (C : Finset V) (hC : C ∈ P.parts) :
    gamma *
        ((C.card : ℝ) -
          ((C ∩ SoficGroups.maximumOverlapPart Q C).card : ℝ)) ≤
      ∑ E ∈ Q.parts,
        (SoficGroups.boundary σ (C ∩ E) : ℝ) := by
  classical
  let D : Finset V := SoficGroups.maximumOverlapPart Q C
  have hCU : C ⊆ U := P.subset hC
  have hD : D ∈ Q.parts :=
    SoficGroups.maximumOverlapPart_mem Q C
      (P.nonempty_of_mem_parts hC) hCU
  have hmax : ∀ E ∈ Q.parts, (C ∩ E).card ≤ (C ∩ D).card :=
    SoficGroups.maximumOverlapPart_maximal Q C
      (P.nonempty_of_mem_parts hC) hCU
  have hsmall (E : Finset V) (hE : E ∈ Q.parts.erase D) :
      gamma * ((C ∩ E).card : ℝ) ≤
        (SoficGroups.boundary σ (C ∩ E) : ℝ) := by
    obtain ⟨hne, hEmem⟩ := Finset.mem_erase.mp hE
    have hdisj : Disjoint (C ∩ E) (C ∩ D) :=
      (Q.disjoint hEmem hD hne).mono
        Finset.inter_subset_right Finset.inter_subset_right
    have hunion : (C ∩ E) ∪ (C ∩ D) ⊆ C :=
      Finset.union_subset Finset.inter_subset_left
        Finset.inter_subset_left
    have hcard :
        (C ∩ E).card + (C ∩ D).card ≤ C.card := by
      rw [← Finset.card_union_of_disjoint hdisj]
      exact Finset.card_le_card hunion
    have hhalf : 2 * (C ∩ E).card ≤ C.card := by
      have hmaximum := hmax E hEmem
      omega
    exact hexp C hC (C ∩ E) Finset.inter_subset_left hhalf
  have hsum :
      (∑ E ∈ Q.parts, ((C ∩ E).card : ℝ)) =
        (C.card : ℝ) := by
    exact_mod_cast
      SoficGroups.sum_card_component_inter_partition Q C hCU
  have herase :
      (∑ E ∈ Q.parts.erase D, ((C ∩ E).card : ℝ)) =
        (C.card : ℝ) - ((C ∩ D).card : ℝ) := by
    have hsplit := Finset.add_sum_erase Q.parts
      (fun E : Finset V => ((C ∩ E).card : ℝ)) hD
    linarith
  change gamma * ((C.card : ℝ) - ((C ∩ D).card : ℝ)) ≤ _
  calc
    gamma * ((C.card : ℝ) - ((C ∩ D).card : ℝ)) =
        ∑ E ∈ Q.parts.erase D,
          gamma * ((C ∩ E).card : ℝ) := by
      rw [← Finset.mul_sum, herase]
    _ ≤ ∑ E ∈ Q.parts.erase D,
          (SoficGroups.boundary σ (C ∩ E) : ℝ) :=
      Finset.sum_le_sum hsmall
    _ ≤ ∑ E ∈ Q.parts,
          (SoficGroups.boundary σ (C ∩ E) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset _ _)
      intro E _ _
      exact Nat.cast_nonneg _
end SoficGroups.KunTransportedAmbientOverlap
