-- Prove2me | solution 1 for SoficGroups.RankArcCharging.rankChangingArc_card_le_crossing_add_unselected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/21288148-07ad-4b35-b0ba-88dd87711387

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_RankArcCharging_rankSupportPreimageBad_card_le
import Theorems.Thm_SoficGroups_RankArcCharging_rankChangingArc_subset_crossing_or_unselected

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
    (P : Finpartition U) (b : V → ℤ) (j : Finset V → ℤ)
    (w : Equiv.Perm V) :
    (rankChangingArc U b w).card ≤
      (partitionWordCrossing P w).card +
        2 * (U \ selectedRankSupport P b j).card := by
  have hsubset := Finset.card_le_card
    (rankChangingArc_subset_crossing_or_unselected P b j w)
  have hfirst := Finset.card_union_le
    (partitionWordCrossing P w) (U \ selectedRankSupport P b j)
  have hsecond := Finset.card_union_le
    (partitionWordCrossing P w ∪ (U \ selectedRankSupport P b j))
    (rankSupportPreimageBad U (selectedRankSupport P b j) w)
  have hpre := rankSupportPreimageBad_card_le
    U (selectedRankSupport P b j) w
  omega
end SoficGroups.RankArcCharging
