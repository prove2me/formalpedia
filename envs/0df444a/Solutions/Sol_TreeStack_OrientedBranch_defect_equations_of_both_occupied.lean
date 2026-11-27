-- Prove2me | solution 1 for TreeStack.OrientedBranch.defect_equations_of_both_occupied
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:48:15.366897+00:00
-- url     : https://prove2.me/submissions/e88e04f4-32f5-490a-8371-6e66e1ed5ff3

import Mathlib
import Definitions.Def_TreeStack_Obstruction
import Definitions.Def_TreeStack_Defect
import Theorems.Thm_TreeStack_scoreDefect_nonneg_iff
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
import Theorems.Thm_TreeStack_OrientedBranch_branchMessage_eq_some_of_occupied
import Theorems.Thm_TreeStack_OrientedBranch_carrier_erase_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_parent
import Theorems.Thm_TreeStack_OrientedBranch_childBranch_root
import Theorems.Thm_TreeStack_OrientedBranch_mem_occupiedChildTasks
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_empty
import Theorems.Thm_TreeStack_OrientedBranch_messageContribution_some
import Theorems.Thm_TreeStack_OrientedBranch_parent_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_carrier
import Theorems.Thm_TreeStack_OrientedBranch_root_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_root_ne_parent
import Theorems.Thm_TreeStack_OrientedBranch_score_eq_effectiveInput_add_reverse
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_of_mem_vertices
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_parent
import Theorems.Thm_TreeStack_OrientedBranch_withBoundary_self
import Theorems.Thm_TreeStack_RootTask_branch_parent
import Theorems.Thm_TreeStack_RootTask_branch_root
import Theorems.Thm_TreeStack_empty_ne_integer_zero
import Theorems.Thm_TreeStack_incidentBranch_parent
import Theorems.Thm_TreeStack_incidentBranch_root
import Theorems.Thm_TreeStack_mass_oneOn
import Theorems.Thm_TreeStack_mem_rootTasks
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
attribute [local simp] TreeStack.RootTask.branch_parent
attribute [local simp] TreeStack.RootTask.branch_root
attribute [local simp] TreeStack.empty_ne_integer_zero
attribute [local simp] TreeStack.incidentBranch_parent
attribute [local simp] TreeStack.incidentBranch_root
attribute [local simp] TreeStack.mass_oneOn
attribute [local simp] TreeStack.mem_rootTasks
attribute [local simp] TreeStack.mem_support_iff
attribute [local simp] TreeStack.oneOn_apply


attribute [local simp] TreeStack.scoreDefect_nonneg_iff

set_option autoImplicit false
open TreeStack
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (B : OrientedBranch T)
    (hB : B.Occupied C)
    (hR : B.reverseBranch.Occupied C) :
    let a :=
      messageContribution (branchMessage C B)
    let b :=
      messageContribution (branchMessage C B.reverseBranch)
    let δu := scoreDefect T C B.root
    let δv := scoreDefect T C B.parent
    a = F (-δu - b) ∧
      b = F (-δv - a) := by
  dsimp
  have hMsgB :=
    branchMessage_eq_some_of_occupied C B hB
  have hMsgR :=
    branchMessage_eq_some_of_occupied C B.reverseBranch hR
  have hScoreB :
      score T C B.root =
        B.effectiveInput C +
          F (B.reverseBranch.effectiveInput C) := by
    simpa [hMsgR] using
      (score_eq_effectiveInput_add_reverse C B)
  have hScoreR :
      score T C B.parent =
        B.reverseBranch.effectiveInput C +
          F (B.effectiveInput C) := by
    have h :=
      score_eq_effectiveInput_add_reverse C B.reverseBranch
    simpa [hMsgB] using h
  simp only [scoreDefect, hMsgB, hMsgR,
    messageContribution_some, neg_neg]
  constructor
  · congr 1
    omega
  · congr 1
    omega
end TreeStack.OrientedBranch
