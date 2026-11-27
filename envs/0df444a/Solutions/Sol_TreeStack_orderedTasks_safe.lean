-- Prove2me | solution 1 for TreeStack.orderedTasks_safe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:39:51.209164+00:00
-- url     : https://prove2.me/submissions/db3e46a4-93a8-4948-9d8b-e0fa24ded583

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_taskGainSum_append
import Theorems.Thm_TreeStack_taskScheduleSafe_append
import Theorems.Thm_TreeStack_taskScheduleSafe_of_all_pos
import Theorems.Thm_TreeStack_taskScheduleSafe_of_all_nonpos_of_final_pos
import Theorems.Thm_TreeStack_taskGainSum_orderedTasks
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
theorem _root_.solution (gain : α → ℤ) (tasks : List α) (a : ℤ)
    (ha : 0 ≤ a)
    (hfinal : 0 < a + taskGainSum gain tasks) :
    TaskScheduleSafe gain a (orderedTasks gain tasks) := by
  let ps := positiveTasks gain tasks
  let zs := zeroTasks gain tasks
  let ns := negativeTasks gain tasks
  have hpos : ∀ t ∈ ps, 0 < gain t := by
    intro t ht
    have ht' : t ∈ tasks ∧ 0 < gain t := by
      simpa [ps, positiveTasks] using ht
    exact ht'.2
  have hnonpos : ∀ t ∈ zs ++ ns, gain t ≤ 0 := by
    intro t ht
    have ht' :
        (t ∈ tasks ∧ gain t = 0) ∨
          (t ∈ tasks ∧ gain t < 0) := by
      simpa [zs, ns, zeroTasks, negativeTasks] using ht
    rcases ht' with ht' | ht' <;> linarith [ht'.2]
  have hsafePos :
      TaskScheduleSafe gain a ps :=
    taskScheduleSafe_of_all_pos gain ha hpos
  have horderedFinal :
      0 < a + taskGainSum gain (orderedTasks gain tasks) := by
    rw [taskGainSum_orderedTasks]
    exact hfinal
  have hrestFinal :
      0 < (a + taskGainSum gain ps) +
        taskGainSum gain (zs ++ ns) := by
    rw [orderedTasks, taskGainSum_append] at horderedFinal
    change
      0 < (a + taskGainSum gain ps) +
        taskGainSum gain (zs ++ ns)
    simpa [ps, zs, ns, add_assoc] using horderedFinal
  have hsafeRest :
      TaskScheduleSafe gain
        (a + taskGainSum gain ps) (zs ++ ns) :=
    taskScheduleSafe_of_all_nonpos_of_final_pos gain
      hrestFinal hnonpos
  rw [orderedTasks, taskScheduleSafe_append]
  simpa [ps, zs, ns] using And.intro hsafePos hsafeRest
end TreeStack
