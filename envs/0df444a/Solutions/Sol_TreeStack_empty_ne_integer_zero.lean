-- Prove2me | solution 1 for TreeStack.empty_ne_integer_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:22.167242+00:00
-- url     : https://prove2.me/submissions/a9fd9327-04a6-43ab-a06b-97b9149fb85c

import Mathlib
import Definitions.Def_TreeStack_Basic
import Definitions.Def_TreeStack_Transfer
import Theorems.Thm_TreeStack_mem_support_iff
attribute [local simp] TreeStack.mem_support_iff



set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution : EMPTY ≠ some 0 := by
  simp [EMPTY]
end TreeStack
