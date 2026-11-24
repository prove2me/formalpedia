-- Prove2me | solution 1 for ULHC.outflow_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:03:14.744016+00:00
-- url     : https://prove2.me/submissions/dee6c756-9600-4a4a-becb-eccb83dbc8af

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn

set_option autoImplicit true
open ULHC
namespace ULHC
theorem _root_.solution (f : Edge → ℤ) (x : Pt) : outflow (fun e => - f e) x = - outflow f x := by
  unfold outflow; ring
end ULHC
