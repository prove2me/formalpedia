-- Prove2me | solution 1 for TreeStack.taskGainSum_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:36:54.480004+00:00
-- url     : https://prove2.me/submissions/d2da5040-92b5-491d-8cd2-26fd586fa680

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
theorem _root_.solution (gain : α → ℤ) (tasks : List α) :
    taskGainSum gain (positiveTasks gain tasks) +
        taskGainSum gain (zeroTasks gain tasks) +
        taskGainSum gain (negativeTasks gain tasks) =
      taskGainSum gain tasks := by
  induction tasks with
  | nil =>
      simp [taskGainSum, positiveTasks, zeroTasks, negativeTasks]
  | cons t ts ih =>
      by_cases hp : 0 < gain t
      · have hz : gain t ≠ 0 := by linarith
        have hn : ¬ gain t < 0 := by linarith
        have ih' := ih
        simp only [positiveTasks, zeroTasks, negativeTasks] at ih'
        simp [taskGainSum, positiveTasks, zeroTasks, negativeTasks,
          hp, hz, hn]
        linarith
      · by_cases hz : gain t = 0
        · have hn : ¬ gain t < 0 := by linarith
          have ih' := ih
          simp only [positiveTasks, zeroTasks, negativeTasks] at ih'
          simp [taskGainSum, positiveTasks, zeroTasks, negativeTasks,
            hp, hz, hn]
          exact ih'
        · have hn : gain t < 0 := by omega
          have ih' := ih
          simp only [positiveTasks, zeroTasks, negativeTasks] at ih'
          simp [taskGainSum, positiveTasks, zeroTasks, negativeTasks,
            hp, hz, hn]
          linarith
end TreeStack
