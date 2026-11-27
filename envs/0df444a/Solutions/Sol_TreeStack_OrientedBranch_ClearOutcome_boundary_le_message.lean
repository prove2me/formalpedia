-- Prove2me | solution 1 for TreeStack.OrientedBranch.ClearOutcome.boundary_le_message
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:56:27.110074+00:00
-- url     : https://prove2.me/submissions/d023f8d1-6dea-42dd-8c8b-78fd60b941b9

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
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_BranchReach_exists_moveSignature
import Theorems.Thm_TreeStack_OrientedBranch_MoveSignature_incoming_parent_eq_boundary
import Theorems.Thm_TreeStack_OrientedBranch_MoveSignature_outgoing_parent_eq_boundary
import Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
import Theorems.Thm_TreeStack_OrientedBranch_signature_branchFlux_bounds
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_OrientedBranch_branchMessage_eq_some_of_occupied
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
attribute [local simp] TreeStack.OrientedBranch.boundaryParityWeight_parent

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
    {D : Configuration V} {d : ℤ}
    (hOcc : B.Occupied C)
    (hMsg : branchMessage C B = some d)
    (hClear : B.ClearOutcome C q D) :
    (D B.parent : ℤ) ≤ (q : ℤ) + d := by
  rcases BranchReach.exists_moveSignature B hClear.1 with
    ⟨m, hmSupp, hmBal, hmPersist⟩
  have hClears : MoveSignature.Clears m C B := by
    intro v hv
    have h := hmBal v
    rw [hClear.2 v hv, B.withBoundary_of_mem_vertices C q hv] at h
    simpa [MoveSignature.BalancesAt] using h.symm
  have hCausal :
      ∀ A : OrientedBranch T,
        A.vertices ⊆ B.vertices →
        A.Occupied C →
        MoveSignature.CausalOutward m A := by
    intro A hAB hAOcc
    apply Nat.pos_of_ne_zero
    intro hzero
    have hAOcc' : A.Occupied (B.withBoundary C q) := by
      rcases hAOcc with ⟨v, hvA, hvpos⟩
      have hvB : v ∈ B.vertices := hAB hvA
      refine ⟨v, hvA, ?_⟩
      simpa [B.withBoundary_of_mem_vertices C q hvB] using hvpos
    have hFinalOcc := hmPersist A hAB hAOcc' hzero
    rcases hFinalOcc with ⟨v, hvA, hvpos⟩
    have hvB : v ∈ B.vertices := hAB hvA
    rw [hClear.2 v hvB] at hvpos
    omega
  have hBound :=
    (signature_branchFlux_bounds m C B hClears hCausal).1 hOcc
  have hMsgCanonical :=
    branchMessage_eq_some_of_occupied C B hOcc
  have hd : d = F (effectiveInput C B) := by
    rw [hMsgCanonical] at hMsg
    exact (Option.some.inj hMsg).symm
  have hParent := hmBal B.parent
  rw [B.withBoundary_parent C q,
    MoveSignature.incoming_parent_eq_boundary B m hmSupp,
    MoveSignature.outgoing_parent_eq_boundary B m hmSupp] at hParent
  have hFlux :
      (D B.parent : ℤ) =
        (q : ℤ) + MoveSignature.boundaryFlux m B := by
    calc
      (D B.parent : ℤ) =
          (q : ℤ) + (m.count B.root B.parent : ℤ) -
            2 * (m.count B.parent B.root : ℤ) := hParent
      _ = (q : ℤ) + MoveSignature.boundaryFlux m B := by
        rw [MoveSignature.boundaryFlux]
        ring
  rw [hFlux, hd]
  linarith [hBound.1]
end ClearOutcome
end TreeStack.OrientedBranch
