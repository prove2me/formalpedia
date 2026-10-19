-- Prove2me | solution 1 for SoficGroups.matched_sum_card_inter_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/0c440cc1-be87-458d-be49-9d8a04f295aa

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (B : Finset V) :
    ∑ C ∈ P.parts, (C ∩ B).card = (U ∩ B).card := by
  have hdis :
      (P.parts : Set (Finset V)).PairwiseDisjoint
        (fun C : Finset V => C ∩ B) := by
    intro C hC D hD hne
    exact (P.disjoint hC hD hne).mono
      Finset.inter_subset_left Finset.inter_subset_left
  have hunion : P.parts.biUnion (fun C => C ∩ B) = U ∩ B := by
    ext x
    simp [← P.biUnion_parts]
    aesop
  calc
    ∑ C ∈ P.parts, (C ∩ B).card =
        (P.parts.biUnion fun C => C ∩ B).card :=
      (Finset.card_biUnion hdis).symm
    _ = (U ∩ B).card := congrArg Finset.card hunion
end SoficGroups
