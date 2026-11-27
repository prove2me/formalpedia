-- Prove2me | solution 1 for TreeStack.two_negative_excess_le_owner_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:05:02.483134+00:00
-- url     : https://prove2.me/submissions/e33a3f2d-79dd-4676-87b8-b04272602c3d

import Mathlib
import Definitions.Def_TreeStack_ForestOwner
import Definitions.Def_TreeStack_DefectCharge

set_option autoImplicit false
open TreeStack
namespace TreeStack
theorem _root_.solution
    {r q deltaOwner weightTail weightOwner : ℤ}
    (hq : 0 ≤ q)
    (hDouble : 2 * weightTail ≤ weightOwner)
    (hDelta : deltaOwner = q + 2 * r) :
    2 * (weightOwner * r + weightTail * q) ≤
      weightOwner * deltaOwner := by
  have hqMul :
      (2 * weightTail) * q ≤ weightOwner * q :=
    mul_le_mul_of_nonneg_right hDouble hq
  rw [hDelta]
  calc
    2 * (weightOwner * r + weightTail * q) =
        2 * weightOwner * r + (2 * weightTail) * q := by
          ring
    _ ≤ 2 * weightOwner * r + weightOwner * q := by
          linarith
    _ = weightOwner * (q + 2 * r) := by
          ring
end TreeStack
