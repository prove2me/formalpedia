-- Prove2me | solution 1 for ValueAwareRR.filteredSum_signReverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:59:41.470567+00:00
-- url     : https://prove2.me/submissions/2baa1870-abe5-46df-bc53-a64084e4cb9d

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_prefixOne_signReverse
import Theorems.Thm_ValueAwareRR_prefixTwo_signReverse
import Theorems.Thm_ValueAwareRR_prefixThree_signReverse

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    filteredSum m (signReverse o) = -filteredSum m o := by
  simp only [filteredSum, prefixOne_signReverse, prefixTwo_signReverse,
    prefixThree_signReverse]
  ring
end ValueAwareRR
