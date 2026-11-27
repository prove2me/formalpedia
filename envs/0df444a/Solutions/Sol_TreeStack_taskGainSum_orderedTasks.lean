-- Prove2me | solution 1 for TreeStack.taskGainSum_orderedTasks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:38:32.216242+00:00
-- url     : https://prove2.me/submissions/c66a68f5-031f-4bd3-af2a-05cda6ad7734

import Mathlib
import Definitions.Def_TreeStack_PebblingMove
import Definitions.Def_TreeStack_Message
import Definitions.Def_TreeStack_Boundary
import Theorems.Thm_TreeStack_taskGainSum_append
import Theorems.Thm_TreeStack_taskGainSum_partition

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
variable {α : Type*}
namespace TreeStack
theorem _root_.solution (gain : α → ℤ) (tasks : List α) :
    taskGainSum gain (orderedTasks gain tasks) =
      taskGainSum gain tasks := by
  rw [orderedTasks, taskGainSum_append, taskGainSum_append]
  linarith [taskGainSum_partition gain tasks]
end TreeStack
