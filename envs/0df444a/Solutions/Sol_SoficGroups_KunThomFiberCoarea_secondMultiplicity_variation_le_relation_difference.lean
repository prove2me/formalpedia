-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.secondMultiplicity_variation_le_relation_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/835912ef-f626-42b9-9847-959c7c97d4e3

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_sum_secondFiber_card
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_natDist_card_le_sdiff
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_secondFiber_sdiff

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (U W : Finset (V × V)) :
    (∑ x : V, Nat.dist (secondMultiplicity U x)
      (secondMultiplicity W x)) ≤
        (U \ W).card + (W \ U).card := by
  classical
  calc
    (∑ x : V, Nat.dist (secondMultiplicity U x)
      (secondMultiplicity W x)) ≤
        ∑ x : V,
          ((secondFiber U x \ secondFiber W x).card +
            (secondFiber W x \ secondFiber U x).card) := by
          apply Finset.sum_le_sum
          intro x _
          exact natDist_card_le_sdiff (secondFiber U x) (secondFiber W x)
    _ = (∑ x : V, (secondFiber (U \ W) x).card) +
          (∑ x : V, (secondFiber (W \ U) x).card) := by
          simp_rw [secondFiber_sdiff]
          rw [Finset.sum_add_distrib]
    _ = (U \ W).card + (W \ U).card := by
          rw [sum_secondFiber_card, sum_secondFiber_card]
end SoficGroups.KunThomFiberCoarea
