-- Prove2me | solution 1 for ULHC.Edge.lo_h
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:23.078261+00:00
-- url     : https://prove2.me/submissions/014e92e2-0c87-4c37-bc27-fdb9f16d219d

import Mathlib
import Definitions.Def_ULHC_Grid

set_option autoImplicit true
open ULHC
namespace ULHC
namespace Edge
theorem _root_.solution (p : Pt) : (Edge.mk .h p).lo = (p.1, p.2 - 1) := rfl
end Edge
end ULHC
