-- Prove2me | solution 1 for TreeStack.oriented_excess_le_tail_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:04:14.629782+00:00
-- url     : https://prove2.me/submissions/0faa8fc4-96e7-4f98-8988-bbfcb0ff1d3c

import Mathlib
import Definitions.Def_TreeStack_ForestOwner
import Definitions.Def_TreeStack_DefectCharge

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution
    {deltaTail deltaHead weightTail : ℤ}
    (hWeight : 0 ≤ weightTail)
    (hBudget : 2 * deltaHead ≤ deltaTail) :
    2 * weightTail * deltaHead ≤ weightTail * deltaTail := by
  have h :=
    mul_le_mul_of_nonneg_left hBudget hWeight
  nlinarith
end TreeStack
