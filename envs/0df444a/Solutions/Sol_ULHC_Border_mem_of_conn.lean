-- Prove2me | solution 1 for ULHC.Border.mem_of_conn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T04:17:43.469807+00:00
-- url     : https://prove2.me/submissions/489004f3-4ee2-465a-8e71-01c9eb6f478d

import Definitions.Def_ULHC_StripCount
import Definitions.Def_ULHC_Walk
import Theorems.Thm_ULHC_Conn_refl


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
namespace Border
theorem _root_.solution {V : Finset Pt} {F : Finset Edge} {P : Finset Pt} (hB : Border V F P)
    {x y : Pt} (hx : x ∈ P) (h : Conn F x y) : y ∈ P := by
  induction h with
  | refl => exact hx
  | tail _ hyz ih => exact hB.2 _ ih _ hyz
end Border
end ULHC
