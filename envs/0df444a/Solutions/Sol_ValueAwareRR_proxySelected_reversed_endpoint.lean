-- Prove2me | solution 1 for ValueAwareRR.proxySelected_reversed_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:15:21.242193+00:00
-- url     : https://prove2.me/submissions/053a148f-d0ef-40ab-ac08-aa4df6c719d5

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_directEndpoint_eq_filtered_div_nine
import Theorems.Thm_ValueAwareRR_proxySelected_reversed_filtered

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) :
    directEndpoint m (signReverse proxySelectedOrder) = 2 * (10 * m + 3) / 81 := by
  rw [directEndpoint_eq_filtered_div_nine, proxySelected_reversed_filtered]
  ring
end ValueAwareRR
