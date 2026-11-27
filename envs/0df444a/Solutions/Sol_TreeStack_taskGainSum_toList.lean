-- Prove2me | solution 1 for TreeStack.taskGainSum_toList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:36:53.569413+00:00
-- url     : https://prove2.me/submissions/51a67816-306f-4f63-85fe-90f1ad648a14

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_taskGainSum_eq_list_sum

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {α : Type*}
namespace TreeStack
theorem _root_.solution [DecidableEq α]
    (gain : α → ℤ) (s : Finset α) :
    taskGainSum gain s.toList = Finset.sum s gain := by
  rw [taskGainSum_eq_list_sum]
  exact Finset.sum_map_toList s gain
end TreeStack
