-- Prove2me | solution 1 for ValueAwareRR.directEndpoint_eq_filtered_div_nine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:01:17.13396+00:00
-- url     : https://prove2.me/submissions/0297f24c-e62b-4964-b5e4-5ff37eb1617d

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_directEndpoint_eq_filtered

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    directEndpoint m o = filteredSum m o / 9 := by
  rw [directEndpoint_eq_filtered]
  norm_num [stepSize]
  ring
end ValueAwareRR
