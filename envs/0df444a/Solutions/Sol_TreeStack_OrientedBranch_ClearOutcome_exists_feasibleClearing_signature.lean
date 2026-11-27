-- Prove2me | solution 1 for TreeStack.OrientedBranch.ClearOutcome.exists_feasibleClearing_signature
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:05:05.41198+00:00
-- url     : https://prove2.me/submissions/573610c5-63e5-41de-b5ac-3467aae01ae4

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_self
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_of_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_occupied_withBoundary_iff
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_BranchReach_exists_moveSignature
import Theorems.Thm_TreeStack_OrientedBranch_MoveSignature_incoming_parent_eq_boundary
import Theorems.Thm_TreeStack_OrientedBranch_MoveSignature_outgoing_parent_eq_boundary
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_support_iff
import Theorems.Thm_TreeStack_oneOn_apply
attribute [local simp] TreeStack.F_three
attribute [local simp] TreeStack.F_two
attribute [local simp] TreeStack.OrientedBranch.childBranch_parent
attribute [local simp] TreeStack.OrientedBranch.childBranch_root
attribute [local simp] TreeStack.OrientedBranch.messageContribution_empty
attribute [local simp] TreeStack.OrientedBranch.messageContribution_some
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
attribute [local simp] TreeStack.empty_ne_integer_zero
attribute [local simp] TreeStack.mass_oneOn
attribute [local simp] TreeStack.mem_support_iff
attribute [local simp] TreeStack.oneOn_apply


attribute [local simp] TreeStack.MoveSignature.zero_count
attribute [local simp] TreeStack.MoveSignature.incoming_zero
attribute [local simp] TreeStack.MoveSignature.outgoing_zero
attribute [local simp] TreeStack.MoveSignature.extend_count_same
attribute [local simp] TreeStack.OrientedBranch.root_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.parent_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.carrier_erase_parent
attribute [local simp] TreeStack.OrientedBranch.withBoundary_parent
attribute [local simp] TreeStack.OrientedBranch.withBoundary_self
attribute [local simp] TreeStack.OrientedBranch.withBoundary_of_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.OccupiedChild.child_vertex
attribute [local simp] TreeStack.OrientedBranch.mem_occupiedChildTasks

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
namespace ClearOutcome
theorem _root_.solution
    (B : OrientedBranch T) (C : Configuration V) (q : ℕ)
    {D : Configuration V} (hOcc : B.Occupied C)
    (hClear : B.ClearOutcome C q D) :
    ∃ m : MoveSignature T,
      MoveSignature.FeasibleClearing m C B ∧
      (D B.parent : ℤ) =
        (q : ℤ) + MoveSignature.boundaryFlux m B := by
  rcases BranchReach.exists_moveSignature B hClear.1 with
    ⟨m, hmSupp, hmBal, hmPersist⟩
  have hClears : MoveSignature.Clears m C B := by
    intro v hv
    have h := hmBal v
    rw [hClear.2 v hv, B.withBoundary_of_mem_vertices C q hv] at h
    simpa [MoveSignature.BalancesAt] using h.symm
  have hCausal : MoveSignature.CausalOutward m B := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hInitialOcc : B.Occupied (B.withBoundary C q) := by
      exact (B.occupied_withBoundary_iff C q).2 hOcc
    have hFinalOcc :=
      hmPersist B (by intro v hv; exact hv) hInitialOcc hzero
    rcases hFinalOcc with ⟨v, hv, hpos⟩
    rw [hClear.2 v hv] at hpos
    omega
  refine ⟨m, ⟨hmSupp, hClears, hCausal⟩, ?_⟩
  have hParent := hmBal B.parent
  rw [B.withBoundary_parent C q,
    MoveSignature.incoming_parent_eq_boundary B m hmSupp,
    MoveSignature.outgoing_parent_eq_boundary B m hmSupp] at hParent
  calc
    (D B.parent : ℤ) =
        (q : ℤ) + (m.count B.root B.parent : ℤ) -
          2 * (m.count B.parent B.root : ℤ) := hParent
    _ = (q : ℤ) + MoveSignature.boundaryFlux m B := by
      rw [MoveSignature.boundaryFlux]
      ring
end ClearOutcome
end TreeStack.OrientedBranch
