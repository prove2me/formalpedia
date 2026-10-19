-- Prove2me | solution 1 for SoficGroups.matchedCore_missing_card_le_symmDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/a75631cf-0cc9-4691-b9b4-0431cca06a2a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_matchedCore_missing_card

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
    (U \ matchedCore R D).card ≤
      (U \ matchedRetainedSupport R).card +
        ∑ C ∈ R, (C ∆ D C).card := by
  rw [matchedCore_missing_card P R hR D]
  exact Nat.add_le_add_left
    (Finset.sum_le_sum fun C _ =>
      Finset.card_le_card (Finset.symmDiff_subset_sdiff (s := C) (t := D C))) _
end SoficGroups
