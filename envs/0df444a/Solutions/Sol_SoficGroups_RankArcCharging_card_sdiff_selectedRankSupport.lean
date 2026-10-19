-- Prove2me | solution 1 for SoficGroups.RankArcCharging.card_sdiff_selectedRankSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/3357a612-a21f-4e6d-bbdb-0e51f33ddb20

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_RankArcCharging_selectedRankSupport_subset
import Theorems.Thm_SoficGroups_RankArcCharging_selectedRankSupport_card

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.RankArcCharging
open scoped BigOperators
namespace SoficGroups.RankArcCharging
theorem _root_.solution
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (j : Finset V → ℤ) :
    (U \ selectedRankSupport P b j).card =
      ∑ C ∈ P.parts,
        (C.card - (C.filter fun x => b x = j C).card) := by
  rw [Finset.card_sdiff_of_subset (selectedRankSupport_subset P b j),
    selectedRankSupport_card]
  rw [Finset.sum_tsub_distrib]
  · rw [P.sum_card_parts]
  · intro C hC
    exact Finset.card_le_card (Finset.filter_subset _ _)
end SoficGroups.RankArcCharging
