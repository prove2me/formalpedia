-- Prove2me | solution 1 for ValueAwareRR.directEndpoint_cast_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:13:51.303889+00:00
-- url     : https://prove2.me/submissions/e8d3f90c-4be1-487c-a764-f7d258e99e77

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_directEndpoint_eq_filtered_div_nine

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (o : SignedOrder) :
    ((directEndpoint m o : ℚ) : ℝ) = ((filteredSum m o : ℚ) : ℝ) / 9 := by
  exact_mod_cast directEndpoint_eq_filtered_div_nine m o
end ValueAwareRR
