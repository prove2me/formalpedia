-- Prove2me | solution 1 for TreeStack.score_pos_of_stackableAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:57:45.335797+00:00
-- url     : https://prove2.me/submissions/1e3021c1-2167-4166-b7a7-7d7dc2bea5d1

import Mathlib
import Definitions.Def_TreeStack_Boundary
import Definitions.Def_TreeStack_RootScore
import Theorems.Thm_TreeStack_incidentBranch_root
import Theorems.Thm_TreeStack_incidentBranch_parent
import Theorems.Thm_TreeStack_RootTask_branch_root
import Theorems.Thm_TreeStack_RootTask_branch_parent
import Theorems.Thm_TreeStack_mem_rootTasks
import Theorems.Thm_TreeStack_Reach_exists_moveSignature
import Theorems.Thm_TreeStack_rootSignatureFluxSum_eq
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_OrientedBranch_BranchReach_exists_moveSignature
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
import Theorems.Thm_TreeStack_OrientedBranch_branchMessage_eq_empty_of_not_occupied
import Theorems.Thm_TreeStack_OrientedBranch_branchMessage_eq_some_of_occupied
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_parent_not_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_signature_branchFlux_bounds
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_of_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_self
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_support_iff
import Theorems.Thm_TreeStack_oneOn_apply
attribute [local simp] TreeStack.F_three
attribute [local simp] TreeStack.F_two
attribute [local simp] TreeStack.MoveSignature.extend_count_same
attribute [local simp] TreeStack.MoveSignature.incoming_zero
attribute [local simp] TreeStack.MoveSignature.outgoing_zero
attribute [local simp] TreeStack.MoveSignature.zero_count
attribute [local simp] TreeStack.OrientedBranch.OccupiedChild.child_vertex
attribute [local simp] TreeStack.OrientedBranch.boundaryParityWeight_parent
attribute [local simp] TreeStack.OrientedBranch.carrier_erase_parent
attribute [local simp] TreeStack.OrientedBranch.childBranch_parent
attribute [local simp] TreeStack.OrientedBranch.childBranch_root
attribute [local simp] TreeStack.OrientedBranch.mem_occupiedChildTasks
attribute [local simp] TreeStack.OrientedBranch.messageContribution_empty
attribute [local simp] TreeStack.OrientedBranch.messageContribution_some
attribute [local simp] TreeStack.OrientedBranch.parent_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.root_mem_carrier
attribute [local simp] TreeStack.OrientedBranch.root_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.root_ne_parent
attribute [local simp] TreeStack.OrientedBranch.withBoundary_of_mem_vertices
attribute [local simp] TreeStack.OrientedBranch.withBoundary_parent
attribute [local simp] TreeStack.OrientedBranch.withBoundary_self
attribute [local simp] TreeStack.empty_ne_integer_zero
attribute [local simp] TreeStack.mass_oneOn
attribute [local simp] TreeStack.mem_support_iff
attribute [local simp] TreeStack.oneOn_apply


attribute [local simp] TreeStack.incidentBranch_root
attribute [local simp] TreeStack.incidentBranch_parent
attribute [local simp] TreeStack.RootTask.branch_root
attribute [local simp] TreeStack.RootTask.branch_parent
attribute [local simp] TreeStack.mem_rootTasks

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack
theorem _root_.solution
    [DecidableEq V]
    (T : FiniteTree V) (C : Configuration V) (r : V)
    (hStackable : StackableAt T.graph C r) :
    0 < score T C r := by
  classical
  rcases hStackable with ⟨D, hReach, hStack⟩
  rcases Reach.exists_moveSignature hReach with
    ⟨m, hmBal, hmPersist⟩
  have hTerm :
      ∀ u : V,
        (m.count u r : ℤ) - 2 * (m.count r u : ℤ) ≤
          rootMessageTerm T C r u := by
    intro u
    by_cases hAdj : T.graph.Adj u r
    · let B : OrientedBranch T := incidentBranch T r u hAdj
      have hClears : OrientedBranch.MoveSignature.Clears m C B := by
        intro w hw
        have hwr : w ≠ r := by
          intro hEq
          subst w
          exact B.parent_not_mem_vertices hw
        have hzero : D w = 0 := hStack.2 w hwr
        have hbal := hmBal w
        rw [hzero] at hbal
        simpa [MoveSignature.BalancesAt] using hbal.symm
      have hCausal :
          ∀ A : OrientedBranch T,
            A.vertices ⊆ B.vertices →
            A.Occupied C →
            OrientedBranch.MoveSignature.CausalOutward m A := by
        intro A hAB hOcc
        apply Nat.pos_of_ne_zero
        intro hzero
        rcases hmPersist A hOcc hzero with ⟨w, hwA, hwpos⟩
        have hwB : w ∈ B.vertices := hAB hwA
        have hwr : w ≠ r := by
          intro hEq
          subst w
          exact B.parent_not_mem_vertices hwB
        have hz : D w = 0 := hStack.2 w hwr
        rw [hz] at hwpos
        omega
      have hBounds :=
        OrientedBranch.signature_branchFlux_bounds
          m C B hClears hCausal
      have hFlux :
          (m.count u r : ℤ) - 2 * (m.count r u : ℤ) =
            OrientedBranch.MoveSignature.boundaryFlux m B := by
        rfl
      rw [hFlux]
      by_cases hOcc : B.Occupied C
      · have hBound := (hBounds.1 hOcc).1
        have hMsg :=
          OrientedBranch.branchMessage_eq_some_of_occupied C B hOcc
        have hTermEq :
            rootMessageTerm T C r u =
              F (OrientedBranch.effectiveInput C B) := by
          rw [rootMessageTerm]
          simp only [dif_pos hAdj]
          change
            OrientedBranch.messageContribution
                (OrientedBranch.branchMessage C B) =
              F (OrientedBranch.effectiveInput C B)
          rw [hMsg]
          rfl
        rw [hTermEq]
        exact hBound
      · rcases hBounds.2 hOcc with ⟨k, hk⟩
        have hMsg :=
          OrientedBranch.branchMessage_eq_empty_of_not_occupied C B hOcc
        have hTermZero : rootMessageTerm T C r u = 0 := by
          rw [rootMessageTerm]
          simp only [dif_pos hAdj]
          change
            OrientedBranch.messageContribution
                (OrientedBranch.branchMessage C B) = 0
          rw [hMsg]
          rfl
        rw [hTermZero, hk]
        omega
    · have hIn : m.count u r = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hpos
        exact hAdj (m.supported hpos)
      have hOut : m.count r u = 0 := by
        apply Nat.eq_zero_of_not_pos
        intro hpos
        exact hAdj (m.supported hpos).symm
      simp [rootMessageTerm, hAdj, hIn, hOut]
  have hFluxLe :
      rootSignatureFluxSum m r ≤ rootMessageSum T C r := by
    rw [rootSignatureFluxSum, rootMessageSum]
    exact Finset.sum_le_sum fun u _ => hTerm u
  have hRootBal := hmBal r
  have hDle : (D r : ℤ) ≤ score T C r := by
    calc
      (D r : ℤ) =
          (C r : ℤ) + (m.incoming r : ℤ) -
            2 * (m.outgoing r : ℤ) := hRootBal
      _ = (C r : ℤ) + rootSignatureFluxSum m r := by
            rw [rootSignatureFluxSum_eq]
            ring
      _ ≤ (C r : ℤ) + rootMessageSum T C r := by
            linarith
      _ = score T C r := rfl
  have hDpos : 0 < (D r : ℤ) := by
    exact_mod_cast hStack.1
  omega
end TreeStack
