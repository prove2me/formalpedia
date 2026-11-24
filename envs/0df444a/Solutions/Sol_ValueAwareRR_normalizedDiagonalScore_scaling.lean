-- Prove2me | solution 1 for ValueAwareRR.normalizedDiagonalScore_scaling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:01:46.315942+00:00
-- url     : https://prove2.me/submissions/8ac5ff2a-40f3-4808-88cc-5d9eac6141b2

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_normalizedPrefixOne_scaling
import Theorems.Thm_ValueAwareRR_normalizedPrefixTwo_scaling
import Theorems.Thm_ValueAwareRR_normalizedPrefixThree_scaling

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    normalizedDiagonalScore m o = normalizationScale m ^ 2 * diagonalScore m o := by
  rw [normalizedDiagonalScore, normalizedPrefixOne_scaling,
    normalizedPrefixTwo_scaling, normalizedPrefixThree_scaling, diagonalScore]
  ring
end ValueAwareRR
