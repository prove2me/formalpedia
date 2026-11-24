-- Prove2me | solution 1 for ULHC.mkBF_cellE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:36:34.447069+00:00
-- url     : https://prove2.me/submissions/1a0a958e-cdb2-4a38-abb1-40e8eaf8506b

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
import Theorems.Thm_ULHC_cellE_frame

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution (c : Pt) (s : Side) :
    cellE c = {(mkBF c s).e1, (mkBF c s).e2, (mkBF c s).l1, (mkBF c s).l2} :=
  cellE_frame c s
end ULHC
