-- Prove2me | solution 1 for ValueAwareRR.normalizedExactLoss_minimizer_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:14:54.982989+00:00
-- url     : https://prove2.me/submissions/0127cf2d-2aa6-4ced-9b7c-6536bb1b099a

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_exactLoss_minimizer_iff
import Theorems.Thm_ValueAwareRR_normalizationScale_pos
import Theorems.Thm_ValueAwareRR_normalizedExactLoss_scaling

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution
    (m : ℚ) (hm : 2 ≤ m) (o : SignedOrder) :
    normalizedExactLoss m o = normalizedExactLoss m trueOptimalOrder ↔
      o = trueOptimalOrder ∨ o = signReverse trueOptimalOrder := by
  rw [normalizedExactLoss_scaling, normalizedExactLoss_scaling]
  have hs2 : 0 < normalizationScale m ^ 2 := sq_pos_of_pos (normalizationScale_pos m hm)
  constructor
  · intro h
    apply (exactLoss_minimizer_iff m hm o).mp
    nlinarith
  · intro h
    rw [(exactLoss_minimizer_iff m hm o).mpr h]
end ValueAwareRR
