-- Prove2me | solution 1 for SoficGroups.matchedRetainedSupport_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/2bf85e51-9850-4db1-a58a-715787e2b5f5

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
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) :
    (matchedRetainedSupport R).card = ∑ C ∈ R, C.card := by
  unfold matchedRetainedSupport
  apply Finset.card_biUnion
  intro C hC E hE hne
  exact P.disjoint (hR hC) (hR hE) hne
end SoficGroups
