-- Prove2me | solution 1 for ValueAwareRR.encodedPermutation_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:15:08.160934+00:00
-- url     : https://prove2.me/submissions/2a50bf40-3ed3-4c59-a00f-073366adc2a1

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_encodedOrders_complete_certificate

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution : Function.Bijective encodedPermutation := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact encodedOrders_complete_certificate
end ValueAwareRR
