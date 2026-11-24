-- Prove2me | solution 1 for ULHC.alt_corners_conn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:10.045811+00:00
-- url     : https://prove2.me/submissions/6b4dd6e4-155b-45f3-9e4f-fde1ea26bb85

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
import Theorems.Thm_ULHC_NoTypeIII_at
import Theorems.Thm_P2M_ULHC_alt_corners_conn__04780e54d852

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hT : NoTypeIII V F) {r : Pt}
    (hr : IsCell V r) (ha : Alt F r) :
    Conn F r (r.1 + 1, r.2) ∧ Conn F r (r.1, r.2 + 1) ∧ Conn F r (r.1 + 1, r.2 + 1) :=
  alt_corners_conn' (hT.at hr) ha
end ULHC
