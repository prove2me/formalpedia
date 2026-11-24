-- Prove2me | solution 1 for ULHC.notTypeIII_of_allConn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:40:24.740573+00:00
-- url     : https://prove2.me/submissions/9b73b50d-8b2e-4659-8680-2a83b47798f6

import Definitions.Def_ULHC_Chain
import Definitions.Def_ULHC_L57
import Theorems.Thm_ULHC_frame_of_allConn

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {d : Pt} (h : AllConn F d) :
    NotTypeIII V F d := fun tf _ _ _ _ => (frame_of_allConn h tf).2.1
end ULHC
