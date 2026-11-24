-- Prove2me | solution 1 for ULHC.Edge.q_v
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:34.088636+00:00
-- url     : https://prove2.me/submissions/a65cc0f6-a602-4588-9397-6546f4494dc3

import Mathlib
import Definitions.Def_ULHC_Grid

set_option autoImplicit true
open ULHC
namespace ULHC
namespace Edge
theorem _root_.solution (p : Pt) : (Edge.mk .v p).q = (p.1, p.2 + 1) := rfl
end Edge
end ULHC
