-- Prove2me | solution 1 for ValueAwareRR.normalizedPrefixTwo_scaling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:55:10.515802+00:00
-- url     : https://prove2.me/submissions/e317f2ed-2f1a-48e3-8de2-6a599d4fc076

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    normalizedPrefixTwo m o = normalizationScale m * prefixTwo m o := by
  simp only [normalizedPrefixTwo, normalizedOrderedResidual, normalizedResidual,
    prefixTwo, orderedResidual]
  ring
end ValueAwareRR
