-- Prove2me | solution 1 for SoficGroups.matchedCore_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/717ac3a0-08e0-4378-9576-35c4e1af30d3

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
    (hR : R ⊆ P.parts) (D : Finset V → Finset V) :
    (matchedCore R D).card = ∑ C ∈ R, (C ∩ D C).card := by
  unfold matchedCore
  apply Finset.card_biUnion
  intro C hC E hE hne
  exact (P.disjoint (hR hC) (hR hE) hne).mono
    Finset.inter_subset_left Finset.inter_subset_left
end SoficGroups
