-- Prove2me | solution 1 for ValueAwareRR.normalizedFilteredSum_scaling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:10:03.539069+00:00
-- url     : https://prove2.me/submissions/42cfe160-6d11-44c0-8ba8-7f3bb2f99284

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_normalizedPrefixOne_scaling
import Theorems.Thm_ValueAwareRR_normalizedPrefixTwo_scaling
import Theorems.Thm_ValueAwareRR_normalizedPrefixThree_scaling

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    normalizedFilteredSum m o = normalizationScale m * filteredSum m o := by
  rw [normalizedFilteredSum, normalizedPrefixOne_scaling, normalizedPrefixTwo_scaling,
    normalizedPrefixThree_scaling, filteredSum]
  ring
end ValueAwareRR
