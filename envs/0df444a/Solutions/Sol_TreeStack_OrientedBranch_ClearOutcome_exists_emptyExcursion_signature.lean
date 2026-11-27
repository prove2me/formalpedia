-- Prove2me | solution 1 for TreeStack.OrientedBranch.ClearOutcome.exists_emptyExcursion_signature
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:05:22.00965+00:00
-- url     : https://prove2.me/submissions/2d77d6ad-1613-4bad-b108-99575334ad73

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
import Theorems.Thm_TreeStack_OrientedBranch_not_occupied_iff_zero_on_vertices
import Theorems.Thm_TreeStack_OrientedBranch_BranchReach_empty_boundary_nonincrease
import Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
import Theorems.Thm_TreeStack_OrientedBranch_BranchReach_empty_boundary_mod_three
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
    {D : Configuration V} (hEmpty : ¬ B.Occupied C)
    (hClear : B.ClearOutcome C q D) :
    ∃ m : MoveSignature T,
      MoveSignature.EmptyExcursion m B ∧
      (D B.parent : ℤ) =
        (q : ℤ) + MoveSignature.boundaryFlux m B ∧
      ∃ k : ℤ, 0 ≤ k ∧ MoveSignature.boundaryFlux m B = -3 * k := by
  rcases BranchReach.exists_moveSignature B hClear.1 with
    ⟨m, hmSupp, hmBal, hmPersist⟩
  have hz := (B.not_occupied_iff_zero_on_vertices C).1 hEmpty
  have hExc : MoveSignature.EmptyExcursion m B := by
    refine ⟨hmSupp, ?_⟩
    intro v hv
    have h := hmBal v
    rw [hClear.2 v hv, B.withBoundary_of_mem_vertices C q hv, hz v hv] at h
    omega
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
  have hNonpos : MoveSignature.boundaryFlux m B ≤ 0 := by
    have hle :=
      BranchReach.empty_boundary_nonincrease B C q hEmpty hClear.1 hClear.2
    omega
  have hBoundaryMod :=
    BranchReach.empty_boundary_mod_three B C q hEmpty hClear.1 hClear.2
  have hFluxMod :
      MoveSignature.boundaryFlux m B ≡ 0 [ZMOD 3] := by
    rw [Int.modEq_iff_dvd] at hBoundaryMod ⊢
    have heq :
        (q : ℤ) - (D B.parent : ℤ) =
          -MoveSignature.boundaryFlux m B := by
      omega
    rw [heq] at hBoundaryMod
    simpa using hBoundaryMod
  have hDvd : (3 : ℤ) ∣ MoveSignature.boundaryFlux m B :=
    Int.modEq_zero_iff_dvd.mp hFluxMod
  rcases hDvd with ⟨a, ha⟩
  have haNonpos : a ≤ 0 := by
    rw [ha] at hNonpos
    omega
  refine ⟨m, hExc, hFlux, -a, by omega, ?_⟩
  rw [ha]
  ring
end ClearOutcome
end TreeStack.OrientedBranch
