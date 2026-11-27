-- Prove2me | solution 1 for TreeStack.oriented_edge_excess_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:57:22.726373+00:00
-- url     : https://prove2.me/submissions/768ec5e8-6809-4819-8da8-f177f7c23bfe

import Mathlib
import Definitions.Def_TreeStack_ForestOwner
import Definitions.Def_TreeStack_DefectCharge

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution
    {a b deltaHead weightTail weightHead : ℤ}
    (ha : 0 ≤ a)
    (hb : b = -2 * (a + deltaHead) - 3)
    (hDouble : 2 * weightTail ≤ weightHead) :
    -(weightHead * a + weightTail * b) ≤
      weightTail + weightHead + 2 * weightTail * deltaHead := by
  have hCoeff : 2 * weightTail - weightHead ≤ 0 := by
    linarith
  have hMul : a * (2 * weightTail - weightHead) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ha hCoeff
  rw [hb]
  calc
    -(weightHead * a + weightTail * (-2 * (a + deltaHead) - 3)) =
        3 * weightTail +
          a * (2 * weightTail - weightHead) +
          2 * weightTail * deltaHead := by
            ring
    _ ≤ 3 * weightTail + 2 * weightTail * deltaHead := by
          linarith
    _ ≤ weightTail + weightHead + 2 * weightTail * deltaHead := by
          linarith
end TreeStack
