-- Prove2me | solution 1 for ULHC.Deg2.class
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:33:33.98741+00:00
-- url     : https://prove2.me/submissions/e62de191-fdbc-47b2-8a50-fa5695cf1a2f

import Definitions.Def_ULHC_Strip
import Definitions.Def_ULHC_StripCount
import Theorems.Thm_ULHC_conn_mem

set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
namespace Deg2
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} (h : Deg2 V F) {a : Pt} (ha : a ∈ V) {z : Pt}
    (hz : Conn F a z) : deg F z = 2 := h.2 z (conn_mem h.1 ha hz)
end Deg2
end ULHC
