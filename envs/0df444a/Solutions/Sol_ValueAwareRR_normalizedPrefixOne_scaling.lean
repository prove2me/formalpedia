-- Prove2me | solution 1 for ValueAwareRR.normalizedPrefixOne_scaling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:55:08.723806+00:00
-- url     : https://prove2.me/submissions/6b5efdb5-d599-4e00-91f4-ed605008bad8

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    normalizedPrefixOne m o = normalizationScale m * prefixOne m o := by
  rfl
end ValueAwareRR
