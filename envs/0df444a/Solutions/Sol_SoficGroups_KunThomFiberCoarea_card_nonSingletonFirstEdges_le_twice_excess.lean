-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.card_nonSingletonFirstEdges_le_twice_excess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/5d186ff6-b9d5-422f-9957-349a45bf6586

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_sum_firstFiber_card
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_firstFiber_nonSingletonFirstEdges

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    (nonSingletonFirstEdges U).card ≤
      2 * ∑ x : V, (firstMultiplicity U x - 1 : ℕ) := by
  classical
  calc
    (nonSingletonFirstEdges U).card =
        ∑ x : V, (firstFiber (nonSingletonFirstEdges U) x).card :=
          (sum_firstFiber_card (nonSingletonFirstEdges U)).symm
    _ = ∑ x : V,
          if firstMultiplicity U x ≠ 1
            then firstMultiplicity U x else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [firstFiber_nonSingletonFirstEdges]
          split <;> simp [firstMultiplicity]
    _ ≤ ∑ x : V, 2 * (firstMultiplicity U x - 1) := by
          apply Finset.sum_le_sum
          intro x _
          split <;> rename_i hx
          · omega
          · omega
    _ = 2 * ∑ x : V, (firstMultiplicity U x - 1) := by
          rw [Finset.mul_sum]
end SoficGroups.KunThomFiberCoarea
