-- Prove2me | solution 1 for SoficGroups.RankArcCharging.selectedRankSupport_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/6f624854-5f5c-495e-8714-71d4955fb41e

import Mathlib
import Definitions.Def_NonSoficGroup

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
    (selectedRankSupport P b j).card =
      ∑ C ∈ P.parts, (C.filter fun x => b x = j C).card := by
  unfold selectedRankSupport
  apply Finset.card_biUnion
  intro C hC D hD hne
  exact (P.disjoint hC hD hne).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)
end SoficGroups.RankArcCharging
