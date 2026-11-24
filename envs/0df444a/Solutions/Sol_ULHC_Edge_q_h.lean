-- Prove2me | solution 1 for ULHC.Edge.q_h
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:33.137113+00:00
-- url     : https://prove2.me/submissions/effd149b-9f8e-4dba-b4e4-d0ab880ef8d8

import Mathlib
import Definitions.Def_ULHC_Grid

set_option autoImplicit true
open ULHC
namespace ULHC
namespace Edge
theorem _root_.solution (p : Pt) : (Edge.mk .h p).q = (p.1 + 1, p.2) := rfl
end Edge
end ULHC
