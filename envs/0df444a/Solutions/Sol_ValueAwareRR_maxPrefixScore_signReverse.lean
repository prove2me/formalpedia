-- Prove2me | solution 1 for ValueAwareRR.maxPrefixScore_signReverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:00:06.079295+00:00
-- url     : https://prove2.me/submissions/522c46b2-593a-4329-a5fd-2ba8bce25aee

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_prefixOne_signReverse
import Theorems.Thm_ValueAwareRR_prefixTwo_signReverse
import Theorems.Thm_ValueAwareRR_prefixThree_signReverse

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    maxPrefixScore m (signReverse o) = maxPrefixScore m o := by
  simp only [maxPrefixScore, prefixOne_signReverse, prefixTwo_signReverse,
    prefixThree_signReverse]
  simp
end ValueAwareRR
