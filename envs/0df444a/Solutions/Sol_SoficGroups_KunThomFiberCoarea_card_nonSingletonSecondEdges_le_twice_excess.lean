-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.card_nonSingletonSecondEdges_le_twice_excess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/a1227ae7-cb5b-445f-aca0-9b2191b7ba0f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_sum_secondFiber_card
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_secondFiber_nonSingletonSecondEdges

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    (nonSingletonSecondEdges U).card ≤
      2 * ∑ x : V, (secondMultiplicity U x - 1 : ℕ) := by
  classical
  calc
    (nonSingletonSecondEdges U).card =
        ∑ x : V, (secondFiber (nonSingletonSecondEdges U) x).card :=
          (sum_secondFiber_card (nonSingletonSecondEdges U)).symm
    _ = ∑ x : V,
          if secondMultiplicity U x ≠ 1
            then secondMultiplicity U x else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [secondFiber_nonSingletonSecondEdges]
          split <;> simp [secondMultiplicity]
    _ ≤ ∑ x : V, 2 * (secondMultiplicity U x - 1) := by
          apply Finset.sum_le_sum
          intro x _
          split <;> rename_i hx
          · omega
          · omega
    _ = 2 * ∑ x : V, (secondMultiplicity U x - 1) := by
          rw [Finset.mul_sum]
end SoficGroups.KunThomFiberCoarea
