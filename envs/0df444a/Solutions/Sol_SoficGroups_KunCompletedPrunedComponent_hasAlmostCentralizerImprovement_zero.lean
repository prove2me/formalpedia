-- Prove2me | solution 1 for SoficGroups.KunCompletedPrunedComponent.hasAlmostCentralizerImprovement_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:58.258203+00:00
-- url     : https://prove2.me/submissions/add96dc5-ffd4-4b5e-b728-220c11b5ff14

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunCompletedPrunedComponent
open scoped BigOperators
namespace SoficGroups.KunCompletedPrunedComponent
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) :
    SoficGroups.HasAlmostCentralizerImprovement σ 0 := by
  refine ⟨fun p hp => ⟨p, ?_, ?_⟩⟩
  · simpa using hp
  · simp
end SoficGroups.KunCompletedPrunedComponent
