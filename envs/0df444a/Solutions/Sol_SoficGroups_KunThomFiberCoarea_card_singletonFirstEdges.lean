-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.card_singletonFirstEdges
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/8b48bdf5-d14d-4cea-ad7b-6ea98a7f760f

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_sum_firstFiber_card
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_firstFiber_singletonFirstEdges

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    (singletonFirstEdges U).card =
      (singletonSupport (firstMultiplicity U)).card := by
  classical
  calc
    (singletonFirstEdges U).card =
        ∑ x : V, (firstFiber (singletonFirstEdges U) x).card :=
          (sum_firstFiber_card (singletonFirstEdges U)).symm
    _ = ∑ x : V, if firstMultiplicity U x = 1 then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [firstFiber_singletonFirstEdges]
          split <;> rename_i hx
          · simpa [firstMultiplicity] using hx
          · simp
    _ = (singletonSupport (firstMultiplicity U)).card := by
          simp [singletonSupport]
end SoficGroups.KunThomFiberCoarea
