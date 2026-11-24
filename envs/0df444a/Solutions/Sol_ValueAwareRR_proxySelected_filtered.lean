-- Prove2me | solution 1 for ValueAwareRR.proxySelected_filtered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T08:54:38.271211+00:00
-- url     : https://prove2.me/submissions/25fce89c-3f0a-446a-b4df-07c10551b3b9

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) :
    filteredSum m proxySelectedOrder = -2 * (10 * m + 3) / 9 := by
  simp [filteredSum, prefixOne, prefixTwo, prefixThree, orderedResidual,
    residual, orderAt, representativeOrder, proxySelectedOrder, contraction,
    familyA, familyB]
  ring
end ValueAwareRR
