-- Prove2me | solution 1 for ULHC.outflow_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:56:10.590222+00:00
-- url     : https://prove2.me/submissions/0f75217b-d58f-44f9-b121-2b4212e7fd0a

import Definitions.Def_ULHC_D
import Definitions.Def_ULHC_Conn

set_option autoImplicit true
open ULHC
namespace ULHC
theorem _root_.solution (f g : Edge → ℤ) (x : Pt) :
    outflow (fun e => f e + g e) x = outflow f x + outflow g x := by
  unfold outflow; ring
end ULHC
