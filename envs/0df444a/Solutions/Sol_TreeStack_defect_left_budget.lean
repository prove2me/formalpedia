-- Prove2me | solution 1 for TreeStack.defect_left_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:52:17.955512+00:00
-- url     : https://prove2.me/submissions/4f23b25a-123e-4384-989f-898e9ae93a1c

import Mathlib
import Definitions.Def_TreeStack_Obstruction
import Definitions.Def_TreeStack_Defect
import Theorems.Thm_TreeStack_defect_left_nonneg

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution
    {a b δu δv : ℤ}
    (hδu : 0 ≤ δu) (hδv : 0 ≤ δv)
    (ha : a = F (-δu - b))
    (hb : b = F (-δv - a))
    (ha0 : 0 ≤ a) :
    2 * δv ≤ δu := by
  rcases (defect_left_nonneg hδu hδv ha hb ha0).2 with h | h
  · omega
  · omega
end TreeStack
