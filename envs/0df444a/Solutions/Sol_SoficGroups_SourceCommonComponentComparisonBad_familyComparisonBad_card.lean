-- Prove2me | solution 1 for SoficGroups.SourceCommonComponentComparisonBad.familyComparisonBad_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/31b252d0-81f1-42f6-93d3-bc22eead23e7

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCommonComponentComparisonBad
open Filter Topology
open scoped BigOperators
namespace SoficGroups.SourceCommonComponentComparisonBad
theorem _root_.solution
    {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    (Q : Finpartition (Finset.univ : Finset V))
    (p : ι → Equiv.Perm V) (eta : ℝ) :
    (familyComparisonBad Q p eta).card =
      ∑ i : ι, (comparisonBad Q (p i) eta).card := by
  classical
  unfold familyComparisonBad
  rw [Finset.card_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i _
  unfold comparisonBad
  rw [Finset.card_filter]
end SoficGroups.SourceCommonComponentComparisonBad
