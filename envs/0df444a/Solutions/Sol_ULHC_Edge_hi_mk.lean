-- Prove2me | solution 1 for ULHC.Edge.hi_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:36:22.207074+00:00
-- url     : https://prove2.me/submissions/a651ce52-b35e-451c-81dc-9568b235c45b

import Mathlib
import Definitions.Def_ULHC_Grid

set_option autoImplicit true
open ULHC
namespace ULHC
namespace Edge
theorem _root_.solution (d : Dir) (p : Pt) : (Edge.mk d p).hi = p := rfl
end Edge
end ULHC
