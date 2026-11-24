-- Prove2me | solution 1 for ValueAwareRR.proxySelectedOrder_maxPrefix_global_minimum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:09:33.278382+00:00
-- url     : https://prove2.me/submissions/11e03904-26e5-44f4-9174-63acf15b0a62

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_maxPrefixScore_signReverse
import Theorems.Thm_ValueAwareRR_maxPrefixScore_table

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    maxPrefixScore m proxySelectedOrder ≤ maxPrefixScore m o := by
  simp only [proxySelectedOrder]
  rcases o with ⟨r, s⟩
  cases s
  · rw [maxPrefixScore_table m hm r, maxPrefixScore_table m hm .BDAC]
    cases r <;> norm_num [maxPrefixTable] <;> nlinarith
  · rw [← maxPrefixScore_signReverse m (r, true)]
    norm_num [signReverse]
    rw [maxPrefixScore_table m hm r, maxPrefixScore_table m hm .BDAC]
    cases r <;> norm_num [maxPrefixTable] <;> nlinarith
end ValueAwareRR
