-- Prove2me | solution 1 for SoficGroups.KunResidualRetainedSelection.exists_matchedRetained_part_boundary_and_bad_density_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/b184a3c1-d69e-4dc0-8967-6fb021883034

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_matchedRetainedSupport_card
import Theorems.Thm_SoficGroups_matched_exists_le_weighted_average
import Theorems.Thm_SoficGroups_matched_sum_card_inter_partition

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualRetainedSelection
open Filter Topology
open scoped BigOperators Pointwise symmDiff
namespace SoficGroups.KunResidualRetainedSelection
theorem _root_.solution
    {V ι : Type*} [DecidableEq V] [Fintype ι]
    (σ : ι → Equiv.Perm V) {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (hRne : R.Nonempty) (B : Finset V) :
    ∃ C ∈ R,
      (SoficGroups.boundary σ C : ℝ) / C.card ≤
        ((∑ D ∈ R, (SoficGroups.boundary σ D : ℝ)) +
          ((SoficGroups.matchedRetainedSupport R ∩ B).card : ℝ)) /
            (SoficGroups.matchedRetainedSupport R).card ∧
      ((C ∩ B).card : ℝ) / C.card ≤
        ((∑ D ∈ R, (SoficGroups.boundary σ D : ℝ)) +
          ((SoficGroups.matchedRetainedSupport R ∩ B).card : ℝ)) /
            (SoficGroups.matchedRetainedSupport R).card := by
  let PR := SoficGroups.matchedRetainedFinpartition P R hR
  have hweight : ∀ C ∈ R, 0 < (C.card : ℝ) := by
    intro C hC
    exact_mod_cast (P.nonempty_of_mem_parts (hR hC)).card_pos
  obtain ⟨C, hC, haverage⟩ :=
    SoficGroups.matched_exists_le_weighted_average R hRne
      (fun C : Finset V => (C.card : ℝ))
      (fun C : Finset V => (SoficGroups.boundary σ C : ℝ) +
        ((C ∩ B).card : ℝ)) hweight
  have hbad :
      (∑ D ∈ R, ((D ∩ B).card : ℝ)) =
        ((SoficGroups.matchedRetainedSupport R ∩ B).card : ℝ) := by
    have h := SoficGroups.matched_sum_card_inter_partition PR B
    exact_mod_cast h
  have hmass :
      (∑ D ∈ R, (D.card : ℝ)) =
        ((SoficGroups.matchedRetainedSupport R).card : ℝ) := by
    exact_mod_cast (SoficGroups.matchedRetainedSupport_card P R hR).symm
  have haverage' :
      ((SoficGroups.boundary σ C : ℝ) + ((C ∩ B).card : ℝ)) /
          C.card ≤
        ((∑ D ∈ R, (SoficGroups.boundary σ D : ℝ)) +
          ((SoficGroups.matchedRetainedSupport R ∩ B).card : ℝ)) /
            (SoficGroups.matchedRetainedSupport R).card := by
    simpa only [Finset.sum_add_distrib, hbad, hmass] using haverage
  have hden : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
  refine ⟨C, hC, ?_, ?_⟩
  · exact (div_le_div_of_nonneg_right
      (le_add_of_nonneg_right (Nat.cast_nonneg (C ∩ B).card)) hden).trans
        haverage'
  · exact (div_le_div_of_nonneg_right
      (le_add_of_nonneg_left
        (Nat.cast_nonneg (SoficGroups.boundary σ C))) hden).trans
        haverage'
end SoficGroups.KunResidualRetainedSelection
