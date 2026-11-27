-- Prove2me | solution 1 for TreeStack.taskScheduleSafe_of_all_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:39:45.181552+00:00
-- url     : https://prove2.me/submissions/1121f3f2-1bb2-4aaa-9c35-77bfa6cef20a

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
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

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {α : Type*}
namespace TreeStack
theorem _root_.solution (gain : α → ℤ) :
    ∀ {a : ℤ} {tasks : List α},
      0 < a →
      (∀ t ∈ tasks, gain t = 0) →
      TaskScheduleSafe gain a tasks
  | _, [], _, _ => by simp [TaskScheduleSafe]
  | a, t :: ts, ha, hzero => by
      have ht : gain t = 0 := hzero t (by simp)
      have hts : ∀ u ∈ ts, gain u = 0 := by
        intro u hu
        exact hzero u (by simp [hu])
      change 0 < a + gain t ∧
        TaskScheduleSafe gain (a + gain t) ts
      constructor
      · simpa [ht] using ha
      · simpa [ht] using
          (solution gain ha hts)
end TreeStack
