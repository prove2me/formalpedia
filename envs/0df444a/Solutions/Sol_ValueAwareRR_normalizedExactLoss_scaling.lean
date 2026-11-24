-- Prove2me | solution 1 for ValueAwareRR.normalizedExactLoss_scaling
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T09:09:24.163738+00:00
-- url     : https://prove2.me/submissions/9ecf7d90-9629-4078-959e-3c7db23ece32

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.normalizedExactLoss_scaling (m : ℚ) (o : SignedOrder) :
    normalizedExactLoss m o = normalizationScale m ^ 2 * exactLoss m o := by
  simp only [normalizedExactLoss, exactLoss, terminalLossFromFiltered, normalizedFilteredSum, filteredSum, normalizedPrefixOne, normalizedPrefixTwo, normalizedPrefixThree, normalizedOrderedResidual, normalizedResidual, prefixOne, prefixTwo, prefixThree, orderedResidual]
  ring


theorem solution (m : ℚ) (o : SignedOrder) :
    normalizedExactLoss m o = normalizationScale m ^ 2 * exactLoss m o := by
  simp only [normalizedExactLoss, exactLoss, terminalLossFromFiltered, normalizedFilteredSum, filteredSum, normalizedPrefixOne, normalizedPrefixTwo, normalizedPrefixThree, normalizedOrderedResidual, normalizedResidual, prefixOne, prefixTwo, prefixThree, orderedResidual]
  ring
