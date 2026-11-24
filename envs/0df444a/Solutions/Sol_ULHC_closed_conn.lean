-- Prove2me | solution 1 for ULHC.closed_conn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:50:20.810123+00:00
-- url     : https://prove2.me/submissions/0ad03ef5-52ac-45d1-90f9-e853fdd749dd

import Definitions.Def_ULHC_Graph
import Definitions.Def_ULHC_Flip
import Theorems.Thm_ULHC_Conn_refl


set_option autoImplicit true
open ULHC
open Finset Classical
namespace ULHC
theorem _root_.solution {F : Finset Edge} {K : Finset Pt} (hK : Closed F K) {x y : Pt} (hx : x ∈ K)
    (h : Conn F x y) : y ∈ K := by
  induction h with
  | refl => exact hx
  | tail _ hyz ih => exact hK _ ih _ hyz
end ULHC
