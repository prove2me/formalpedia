-- Prove2me | solution 1 for TreeStack.two_negative_edge_excess_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:04:44.469325+00:00
-- url     : https://prove2.me/submissions/f0ca468a-f2be-4dc6-8be4-507b203f9b91

import Mathlib
import Definitions.Def_TreeStack_ForestOwner
import Definitions.Def_TreeStack_DefectCharge

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution
    {a b r q weightTail weightHead : ℤ}
    (ha : a = -(2 * r + 1))
    (hb : b = -(2 * q + 1)) :
    -(weightHead * a + weightTail * b) =
      weightTail + weightHead +
        2 * (weightHead * r + weightTail * q) := by
  rw [ha, hb]
  ring
end TreeStack
