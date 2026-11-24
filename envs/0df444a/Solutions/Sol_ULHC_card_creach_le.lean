-- Prove2me | solution 1 for ULHC.card_creach_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:25:39.660771+00:00
-- url     : https://prove2.me/submissions/88d30702-68fb-4ac0-9ab5-656f4b4b63fd

import Definitions.Def_ULHC_Algorithm
import Definitions.Def_ULHC_CostConn
import Theorems.Thm_ULHC_creach_subI
import Theorems.Thm_ULHC_Conn_trans
import Theorems.Thm_ULHC_DWalk_trans


set_option autoImplicit true
open ULHC
open Finset
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hFV : Inside V F) (x : Pt) (k : ℕ) :
    (creach F x k).card ≤ V.card + 1 :=
  (card_le_card (creach_subI hFV x k)).trans (card_insert_le _ _)
end ULHC
