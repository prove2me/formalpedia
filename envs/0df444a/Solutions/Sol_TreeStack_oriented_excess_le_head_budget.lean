-- Prove2me | solution 1 for TreeStack.oriented_excess_le_head_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:04:15.107728+00:00
-- url     : https://prove2.me/submissions/a5cc9434-af16-4895-acb2-a7abcea031f6

import Mathlib
import Definitions.Def_TreeStack_ForestOwner
import Definitions.Def_TreeStack_DefectCharge

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution
    {deltaHead weightTail weightHead : ℤ}
    (hDelta : 0 ≤ deltaHead)
    (hDouble : 2 * weightTail ≤ weightHead) :
    2 * weightTail * deltaHead ≤ weightHead * deltaHead := by
  exact mul_le_mul_of_nonneg_right hDouble hDelta
end TreeStack
