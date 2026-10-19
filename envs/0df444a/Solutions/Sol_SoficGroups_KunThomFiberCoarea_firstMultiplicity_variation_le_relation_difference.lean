-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.firstMultiplicity_variation_le_relation_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/93d177ac-b553-4ddb-8edf-f5ef8162340a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_sum_firstFiber_card
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_natDist_card_le_sdiff
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_firstFiber_sdiff

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (U W : Finset (V × V)) :
    (∑ x : V, Nat.dist (firstMultiplicity U x)
      (firstMultiplicity W x)) ≤
        (U \ W).card + (W \ U).card := by
  classical
  calc
    (∑ x : V, Nat.dist (firstMultiplicity U x)
      (firstMultiplicity W x)) ≤
        ∑ x : V,
          ((firstFiber U x \ firstFiber W x).card +
            (firstFiber W x \ firstFiber U x).card) := by
          apply Finset.sum_le_sum
          intro x _
          exact natDist_card_le_sdiff (firstFiber U x) (firstFiber W x)
    _ = (∑ x : V, (firstFiber (U \ W) x).card) +
          (∑ x : V, (firstFiber (W \ U) x).card) := by
          simp_rw [firstFiber_sdiff]
          rw [Finset.sum_add_distrib]
    _ = (U \ W).card + (W \ U).card := by
          rw [sum_firstFiber_card, sum_firstFiber_card]
end SoficGroups.KunThomFiberCoarea
