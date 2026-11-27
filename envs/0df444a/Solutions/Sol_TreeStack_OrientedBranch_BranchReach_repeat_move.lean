-- Prove2me | solution 1 for TreeStack.OrientedBranch.BranchReach.repeat_move
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:35:44.134063+00:00
-- url     : https://prove2.me/submissions/966f40d7-8278-46db-aa6c-ba9b14479ab9

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

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
variable [DecidableEq V]
namespace TreeStack.OrientedBranch
namespace BranchReach
theorem _root_.solution
    (B : OrientedBranch T) {u v : V}
    (huv : T.graph.Adj u v)
    (huCarrier : u ∈ B.carrier) (hvCarrier : v ∈ B.carrier) :
    ∀ (C : Configuration V) (n : ℕ),
      2 * n ≤ C u →
      ∃ D : Configuration V,
        B.BranchReach C D ∧
        D u = C u - 2 * n ∧
        D v = C v + n ∧
        (∀ w : V, w ≠ u → w ≠ v → D w = C w) := by
  classical
  intro C n
  induction n generalizing C with
  | zero =>
      intro h
      refine ⟨C, Relation.ReflTransGen.refl, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro w hwu hwv
        rfl
  | succ n ih =>
      intro hTotal
      have hLegal : 2 ≤ C u := by omega
      let E : Configuration V := move C u v
      have hStep : B.BranchPebbleStep C E :=
        ⟨u, v, huv, hLegal, huCarrier, hvCarrier, rfl⟩
      have hReachStep : B.BranchReach C E :=
        Relation.ReflTransGen.single hStep
      have hEu : E u = C u - 2 := by
        simp [E, move, huv.ne]
      have hEv : E v = C v + 1 := by
        simp [E, move, huv.ne]
      have hRemain : 2 * n ≤ E u := by
        rw [hEu]
        omega
      rcases ih E hRemain with ⟨D, hReachRest, hDu, hDv, hOther⟩
      have hReach : B.BranchReach C D :=
        Relation.ReflTransGen.trans hReachStep hReachRest
      refine ⟨D, hReach, ?_, ?_, ?_⟩
      · rw [hDu, hEu]
        omega
      · rw [hDv, hEv]
        omega
      · intro w hwu hwv
        rw [hOther w hwu hwv]
        simp [E, move, hwu, hwv]
end BranchReach
end TreeStack.OrientedBranch
