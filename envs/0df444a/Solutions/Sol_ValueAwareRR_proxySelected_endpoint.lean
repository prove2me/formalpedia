-- Prove2me | solution 1 for ValueAwareRR.proxySelected_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:14:49.295305+00:00
-- url     : https://prove2.me/submissions/b1198f32-fb22-4f52-adaa-e2a3977e3734

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_directEndpoint_eq_filtered_div_nine
import Theorems.Thm_ValueAwareRR_proxySelected_filtered

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) :
    directEndpoint m proxySelectedOrder = -2 * (10 * m + 3) / 81 := by
  rw [directEndpoint_eq_filtered_div_nine, proxySelected_filtered]
  ring
end ValueAwareRR
