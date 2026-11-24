-- Prove2me | solution 1 for ULHC.twoFactorCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:32:23.874079+00:00
-- url     : https://prove2.me/submissions/984d8ccc-3a08-4013-b04d-b70b7f1cc212

import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_CostTwoFactor
import Theorems.Thm_ULHC_augLoopCost_le

set_option autoImplicit true
open ULHC
open Finset TF
namespace ULHC
theorem _root_.solution (V : Finset Pt) : twoFactorCost V ≤ 200 * (V.card + 1) ^ 3 := by
  have := augLoopCost_le V (V.card + 1) ∅
  unfold twoFactorCost degCost
  nlinarith
end ULHC
