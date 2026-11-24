-- Prove2me | solution 1 for ULHC.Edge.lo_v
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:23.643319+00:00
-- url     : https://prove2.me/submissions/a53b86fe-0a88-49fc-969b-8ae410845381

import Mathlib
import Definitions.Def_ULHC_Grid

set_option autoImplicit true
open ULHC
namespace ULHC
namespace Edge
theorem _root_.solution (p : Pt) : (Edge.mk .v p).lo = (p.1 - 1, p.2) := rfl
end Edge
end ULHC
