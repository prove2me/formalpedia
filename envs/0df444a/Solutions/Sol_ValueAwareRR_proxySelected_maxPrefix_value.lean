-- Prove2me | solution 1 for ValueAwareRR.proxySelected_maxPrefix_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T09:16:30.383798+00:00
-- url     : https://prove2.me/submissions/4c19ae0c-3898-4771-b433-bc394d21dcdf

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
import Theorems.Thm_ValueAwareRR_maxPrefixScore_table

set_option autoImplicit true
open ValueAwareRR
namespace ValueAwareRR
theorem _root_.solution (m : ℚ) (hm : 2 ≤ m) :
    maxPrefixScore m proxySelectedOrder = 2 * m := by
  simpa [proxySelectedOrder, maxPrefixTable] using maxPrefixScore_table m hm .BDAC
end ValueAwareRR
