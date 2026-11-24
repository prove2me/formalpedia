-- Prove2me | solution 1 for ULHC.gsrcCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:34:15.187+00:00
-- url     : https://prove2.me/submissions/abc77543-8339-42cf-890f-ac7351157901

import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_CostStrips
import Theorems.Thm_ULHC_allStripsCost_le
import Theorems.Thm_ULHC_connBCost_le


set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (hGV : Inside V G) (x : Node) : gsrcCost V G x ≤ 160 * (V.card + 1) ^ 2 := by
  have h1 := allStripsCost_le V G
  have h2 := connBCost_le hGV (back1 x.σ.c x.σ.s)
  have hN1 : 1 ≤ (V.card + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  unfold gsrcCost validBCost
  nlinarith
end ULHC
