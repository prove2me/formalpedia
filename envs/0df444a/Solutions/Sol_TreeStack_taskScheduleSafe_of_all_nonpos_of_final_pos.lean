-- Prove2me | solution 1 for TreeStack.taskScheduleSafe_of_all_nonpos_of_final_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:37:32.06246+00:00
-- url     : https://prove2.me/submissions/33be0f91-e999-409e-8a88-5e754ddbfc0c

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_MoveSignature_zero_count
import Theorems.Thm_TreeStack_MoveSignature_incoming_zero
import Theorems.Thm_TreeStack_MoveSignature_outgoing_zero
import Theorems.Thm_TreeStack_MoveSignature_extend_count_same
import Theorems.Thm_TreeStack_taskGainSum_nonpos
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
theorem _root_.solution
    (gain : α → ℤ) :
    ∀ {a : ℤ} {tasks : List α},
      0 < a + taskGainSum gain tasks →
      (∀ t ∈ tasks, gain t ≤ 0) →
      TaskScheduleSafe gain a tasks
  | _, [], _, _ => by simp [TaskScheduleSafe]
  | a, t :: ts, hfinal, hnonpos => by
      have ht : gain t ≤ 0 := hnonpos t (by simp)
      have hts : ∀ u ∈ ts, gain u ≤ 0 := by
        intro u hu
        exact hnonpos u (by simp [hu])
      have htail := taskGainSum_nonpos gain ts hts
      have hfirst : 0 < a + gain t := by
        simp only [taskGainSum] at hfinal
        linarith
      change 0 < a + gain t ∧
        TaskScheduleSafe gain (a + gain t) ts
      refine ⟨hfirst, ?_⟩
      apply solution gain
      · simp only [taskGainSum] at hfinal
        linarith
      · exact hts
end TreeStack
