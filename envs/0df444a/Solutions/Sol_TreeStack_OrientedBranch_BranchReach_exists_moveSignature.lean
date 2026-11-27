-- Prove2me | solution 1 for TreeStack.OrientedBranch.BranchReach.exists_moveSignature
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:43:11.005604+00:00
-- url     : https://prove2.me/submissions/3e171af6-2a9e-4213-920f-0e1baf40d8d2

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_MoveSignature_incoming_extend
import Theorems.Thm_TreeStack_MoveSignature_outgoing_extend
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_self
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_of_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_MoveSignature_zero_supportedOn
import Theorems.Thm_TreeStack_OrientedBranch_MoveSignature_extend_supportedOn
import Theorems.Thm_TreeStack_OrientedBranch_move_balance_int
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_edge_leaving_vertices_eq_boundary
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_parent_not_mem_vertices
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
namespace BranchReach
theorem _root_.solution
    (B : OrientedBranch T) {C D : Configuration V}
    (hreach : B.BranchReach C D) :
    ∃ m : MoveSignature T,
      MoveSignature.SupportedOn m B ∧
      (∀ w : V,
        (D w : ℤ) =
          (C w : ℤ) + (m.incoming w : ℤ) -
            2 * (m.outgoing w : ℤ)) ∧
      (∀ A : OrientedBranch T,
        A.vertices ⊆ B.vertices →
        A.Occupied C →
        m.count A.root A.parent = 0 →
        A.Occupied D) := by
  induction hreach with
  | refl =>
      refine ⟨MoveSignature.zero T, MoveSignature.zero_supportedOn B, ?_, ?_⟩
      · intro w
        simp
      · intro A _ hOcc _
        exact hOcc
  | tail hCE hED ih =>
      rcases hED with ⟨u, v, huv, hlegal, huCarrier, hvCarrier, rfl⟩
      rcases ih with ⟨m, hmSupp, hmBal, hmPersist⟩
      let m' : MoveSignature T := m.extend u v huv
      refine ⟨m', ?_, ?_, ?_⟩
      · exact MoveSignature.extend_supportedOn B m huv hmSupp huCarrier hvCarrier
      · intro w
        rw [move_balance_int _ huv.ne hlegal w, hmBal w]
        simp [m', MoveSignature.incoming_extend, MoveSignature.outgoing_extend]
        by_cases hwu : w = u <;> simp [hwu] <;> ring
      · intro A hAB hOcc hzero
        have hmzero : m.count A.root A.parent = 0 := by
          have hle :
              m.count A.root A.parent ≤ m'.count A.root A.parent := by
            dsimp [m', MoveSignature.extend]
            omega
          omega
        rcases hmPersist A hAB hOcc hmzero with ⟨w, hwA, hwpos⟩
        by_cases hvA : v ∈ A.vertices
        · refine ⟨v, hvA, ?_⟩
          simp [move, huv.ne]
        · have huA : u ∉ A.vertices := by
            intro huA
            have hEdge :=
              A.edge_leaving_vertices_eq_boundary huA hvA huv
            rw [Sym2.eq_iff] at hEdge
            rcases hEdge with h | h
            · rcases h with ⟨huRoot, hvParent⟩
              subst u
              subst v
              dsimp [m', MoveSignature.extend] at hzero
              simp at hzero
            · rcases h with ⟨huParent, hvRoot⟩
              subst u
              exact A.parent_not_mem_vertices huA
          have hwu : w ≠ u := by
            intro h
            subst w
            exact huA hwA
          have hwv : w ≠ v := by
            intro h
            subst w
            exact hvA hwA
          refine ⟨w, hwA, ?_⟩
          simpa [move, hwu, hwv] using hwpos
end BranchReach
end TreeStack.OrientedBranch
