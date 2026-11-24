-- Prove2me | solution 1 for ValueAwareRR.normalizedProxy_maxPrefix_global_minimum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:11:58.394549+00:00
-- url     : https://prove2.me/submissions/6dcebd2b-1c6a-4f23-9e19-7939eec16ef9

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_proxySelectedOrder_maxPrefix_global_minimum
import Theorems.Thm_ValueAwareRR_normalizationScale_pos
import Theorems.Thm_ValueAwareRR_normalizedMaxPrefixScore_scaling

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    normalizedMaxPrefixScore m proxySelectedOrder ≤ normalizedMaxPrefixScore m o := by
  rw [normalizedMaxPrefixScore_scaling m hm,
    normalizedMaxPrefixScore_scaling m hm]
  exact mul_le_mul_of_nonneg_left
    (proxySelectedOrder_maxPrefix_global_minimum m hm o)
    (normalizationScale_pos m hm).le
end ValueAwareRR
