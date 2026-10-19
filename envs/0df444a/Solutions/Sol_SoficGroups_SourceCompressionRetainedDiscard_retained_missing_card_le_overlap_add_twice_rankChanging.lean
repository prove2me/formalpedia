-- Prove2me | solution 1 for SoficGroups.SourceCompressionRetainedDiscard.retained_missing_card_le_overlap_add_twice_rankChanging
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/2d75234d-787f-4f80-b8da-9521f7b50959

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_matchedRetainedSupport_subset
import Theorems.Thm_SoficGroups_matchedRetainedSupport_card
import Theorems.Thm_SoficGroups_SourceCompressionRetainedDiscard_overlapBad_disjoint_witnesslessComponents
import Theorems.Thm_SoficGroups_SourceCompressionRetainedDiscard_witnesslessComponents_mass_le_twice_rankChanging

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
    ((Finset.univ : Finset V) \
      SoficGroups.matchedRetainedSupport
        (retainedComponents P Q T b eta)).card ≤
      (∑ C ∈ SoficGroups.insufficientOverlapComponents P Q eta, C.card) +
        2 * (SoficGroups.RankArcCharging.rankChangingArc
          (Finset.univ : Finset V) b T.symm).card := by
  let O := SoficGroups.insufficientOverlapComponents P Q eta
  let W := witnesslessComponents P Q T b eta
  let R := retainedComponents P Q T b eta
  let B := SoficGroups.RankArcCharging.rankChangingArc
    (Finset.univ : Finset V) b T.symm
  have hR : R ⊆ P.parts := Finset.sdiff_subset
  have hmiss :
      ((Finset.univ : Finset V) \
        SoficGroups.matchedRetainedSupport R).card =
          ∑ C ∈ P.parts \ R, C.card := by
    have hsplit :
        (∑ C ∈ P.parts \ R, C.card) +
          (∑ C ∈ R, C.card) =
            ∑ C ∈ P.parts, C.card :=
      Finset.sum_sdiff hR
    have hcover := P.sum_card_parts
    have hret := SoficGroups.matchedRetainedSupport_card P R hR
    have hcard := Finset.card_sdiff_add_card_eq_card
      (SoficGroups.matchedRetainedSupport_subset P R hR)
    omega
  have hsubset : P.parts \ R ⊆ O ∪ W := by
    intro C hC
    have hC' := Finset.mem_sdiff.mp hC
    by_contra hbad
    apply hC'.2
    change C ∈ P.parts \ (O ∪ W)
    exact Finset.mem_sdiff.mpr ⟨hC'.1, hbad⟩
  have hsum :
      (∑ C ∈ P.parts \ R, C.card) ≤
        ∑ C ∈ O ∪ W, C.card :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ => Nat.zero_le _)
  have hdis : Disjoint O W :=
    overlapBad_disjoint_witnesslessComponents P Q T b eta
  have hunion :
      (∑ C ∈ O ∪ W, C.card) =
        (∑ C ∈ O, C.card) + (∑ C ∈ W, C.card) :=
    Finset.sum_union hdis
  have hwitness : (∑ C ∈ W, C.card) ≤ 2 * B.card :=
    witnesslessComponents_mass_le_twice_rankChanging
      P Q T b eta heta
  change
    ((Finset.univ : Finset V) \
      SoficGroups.matchedRetainedSupport R).card ≤
        (∑ C ∈ O, C.card) + 2 * B.card
  omega
end SoficGroups.SourceCompressionRetainedDiscard
