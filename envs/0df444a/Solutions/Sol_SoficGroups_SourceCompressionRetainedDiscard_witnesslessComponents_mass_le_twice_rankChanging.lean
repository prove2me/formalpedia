-- Prove2me | solution 1 for SoficGroups.SourceCompressionRetainedDiscard.witnesslessComponents_mass_le_twice_rankChanging
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/5abe82a4-7264-443d-a927-b180634f0eba

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_matched_sum_card_inter_partition
import Theorems.Thm_SoficGroups_SourceCompressionRetainedDiscard_witnesslessComponents_subset_parts
import Theorems.Thm_SoficGroups_SourceCompressionRetainedDiscard_witnessless_component_card_le_twice_rankChanging

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionRetainedDiscard
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.SourceCompressionRetainedDiscard
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : Finpartition (Finset.univ : Finset V))
    (T : Equiv.Perm V) (b : V → ℤ)
    (eta : ℝ) (heta : eta ≤ (1 : ℝ) / 2) :
    (∑ C ∈ witnesslessComponents P Q T b eta, C.card) ≤
      2 * (SoficGroups.RankArcCharging.rankChangingArc
        (Finset.univ : Finset V) b T.symm).card := by
  let B := SoficGroups.RankArcCharging.rankChangingArc
    (Finset.univ : Finset V) b T.symm
  have hsum :
      (∑ C ∈ witnesslessComponents P Q T b eta, (C ∩ B).card) ≤
        ∑ C ∈ P.parts, (C ∩ B).card := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (witnesslessComponents_subset_parts P Q T b eta)
      (fun _ _ _ => Nat.zero_le _)
  have hpartition :
      (∑ C ∈ P.parts, (C ∩ B).card) = B.card := by
    simpa using SoficGroups.matched_sum_card_inter_partition P B
  calc
    (∑ C ∈ witnesslessComponents P Q T b eta, C.card) ≤
        ∑ C ∈ witnesslessComponents P Q T b eta,
          2 * (C ∩ B).card := by
      exact Finset.sum_le_sum fun C hC =>
        witnessless_component_card_le_twice_rankChanging
          P Q T b eta heta C hC
    _ = 2 * (∑ C ∈ witnesslessComponents P Q T b eta,
          (C ∩ B).card) := by
      simp [Finset.mul_sum]
    _ ≤ 2 * (∑ C ∈ P.parts, (C ∩ B).card) :=
      Nat.mul_le_mul_left 2 hsum
    _ = 2 * B.card := by rw [hpartition]
end SoficGroups.SourceCompressionRetainedDiscard
