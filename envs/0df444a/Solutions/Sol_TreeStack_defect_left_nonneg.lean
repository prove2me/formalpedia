-- Prove2me | solution 1 for TreeStack.defect_left_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:46:41.3201+00:00
-- url     : https://prove2.me/submissions/c5b530c1-9921-4a1e-a373-401274bcac5e

import Mathlib
import Definitions.Def_TreeStack_Obstruction
import Definitions.Def_TreeStack_Defect
import Theorems.Thm_TreeStack_F_eq_nonneg_iff
import Theorems.Thm_TreeStack_F_of_le_one
import Theorems.Thm_TreeStack_F_three
import Theorems.Thm_TreeStack_F_two
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_OrientedBranch_OccupiedChild_child_vertex
import Theorems.Thm_TreeStack_OrientedBranch_boundaryParityWeight_parent
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



set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a))
    (ha0 : 0 ≤ a) :
    b = -2 * (a + δv) - 3 ∧
      (δu = 2 * δv ∨
        (0 < a ∧ δu = 2 * δv + 3)) := by
  have hinB : -δv - a ≤ 1 := by
    omega
  have hb' : b = 2 * (-δv - a) - 3 := by
    simpa only [F_of_le_one hinB] using hb
  have hpre :
      (0 < a ∧ -δu - b = 2 * a) ∨
        -δu - b = 2 * a + 3 := by
    exact
      (F_eq_nonneg_iff
        (z := -δu - b) (k := a) ha0).1 ha.symm
  refine ⟨?_, ?_⟩
  · omega
  · rcases hpre with hpre | hpre
    · right
      exact ⟨hpre.1, by omega⟩
    · left
      omega
end TreeStack
