-- Prove2me | solution 1 for ULHC.Inside.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:45:01.280334+00:00
-- url     : https://prove2.me/submissions/c22e4bcd-18cf-42d3-bfa9-ed8e14f54308

import Definitions.Def_ULHC_Planar
import Definitions.Def_ULHC_Graph

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
namespace Inside
theorem _root_.solution {V : Finset Pt} {F F' : Finset Edge} (h : Inside V F) (hs : F' ⊆ F) :
    Inside V F' := fun e he => h e (hs he)
end Inside
end ULHC
