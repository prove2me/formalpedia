-- Prove2me | solution 1 for ValueAwareRR.normalizedPrefixThree_scaling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:55:58.689885+00:00
-- url     : https://prove2.me/submissions/f4b4227e-74b0-42f0-9315-c8076396d1e5

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    normalizedPrefixThree m o = normalizationScale m * prefixThree m o := by
  simp only [normalizedPrefixThree, normalizedOrderedResidual, normalizedResidual,
    prefixThree, orderedResidual]
  ring
end ValueAwareRR
