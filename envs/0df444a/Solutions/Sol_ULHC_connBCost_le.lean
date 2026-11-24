-- Prove2me | solution 1 for ULHC.connBCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:31:06.707207+00:00
-- url     : https://prove2.me/submissions/ca697e66-2bbb-4697-9bca-bd8edac994e9

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_CostConn
import Theorems.Thm_ULHC_creachCost_le

set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hFV : Inside V F) (x : Pt) :
    connBCost V F x ≤ 30 * (V.card + 1) ^ 2 := by
  unfold connBCost cclsCost
  have := creachCost_le hFV x V.card
  nlinarith
end ULHC
