-- Prove2me | solution 1 for ULHC.NoTypeIII.at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:20:13.094604+00:00
-- url     : https://prove2.me/submissions/bf97d97a-40ac-434a-b040-7fed4111b323

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
namespace NoTypeIII
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (hT : NoTypeIII V F) {c : Pt}
    (hc : IsCell V c) : NotTypeIII V F c := hT c hc
end NoTypeIII
end ULHC
