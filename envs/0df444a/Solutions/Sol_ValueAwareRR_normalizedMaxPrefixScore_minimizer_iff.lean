-- Prove2me | solution 1 for ValueAwareRR.normalizedMaxPrefixScore_minimizer_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:12:14.273925+00:00
-- url     : https://prove2.me/submissions/baec90df-8b0e-4e62-a4cd-84d9a43559ec

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_maxPrefixScore_minimizer_iff
import Theorems.Thm_ValueAwareRR_normalizationScale_pos
import Theorems.Thm_ValueAwareRR_normalizedMaxPrefixScore_scaling

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    normalizedMaxPrefixScore m o = normalizedMaxPrefixScore m proxySelectedOrder ↔
      o = proxySelectedOrder ∨ o = signReverse proxySelectedOrder := by
  rw [normalizedMaxPrefixScore_scaling m hm,
    normalizedMaxPrefixScore_scaling m hm]
  have hs : 0 < normalizationScale m := normalizationScale_pos m hm
  constructor
  · intro h
    apply (maxPrefixScore_minimizer_iff m hm o).mp
    nlinarith
  · intro h
    rw [(maxPrefixScore_minimizer_iff m hm o).mpr h]
end ValueAwareRR
