-- Prove2me | solution 1 for SoficGroups.matchedCore_missing_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/237636c8-1d24-4a37-8298-9487b1c61433

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_matchedRetainedSupport_subset
import Theorems.Thm_SoficGroups_matchedCore_subset
import Theorems.Thm_SoficGroups_matchedRetainedSupport_card
import Theorems.Thm_SoficGroups_matchedCore_card

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
    (U \ matchedCore R D).card =
      (U \ matchedRetainedSupport R).card +
        ∑ C ∈ R, (C \ D C).card := by
  have hcore := Finset.card_sdiff_add_card_eq_card
    (matchedCore_subset P R hR D)
  have hret := Finset.card_sdiff_add_card_eq_card
    (matchedRetainedSupport_subset P R hR)
  have hsplit :
      (∑ C ∈ R, (C \ D C).card) + (matchedCore R D).card =
        (matchedRetainedSupport R).card := by
    rw [matchedCore_card P R hR D, matchedRetainedSupport_card P R hR]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun C _ =>
      Finset.card_sdiff_add_card_inter C (D C)
  omega
end SoficGroups
