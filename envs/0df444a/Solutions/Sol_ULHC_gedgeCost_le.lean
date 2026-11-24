-- Prove2me | solution 1 for ULHC.gedgeCost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:39.222168+00:00
-- url     : https://prove2.me/submissions/eee4eccc-855e-406f-a258-d46c13fd6bd9

import Definitions.Def_ULHC_CostConn
import Definitions.Def_ULHC_AlgComplete
import Definitions.Def_ULHC_CostStrips
import Theorems.Thm_ULHC_node_len
import Theorems.Thm_ULHC_cr2BCost_le

set_option autoImplicit true
open ULHC
open Finset
variable {V : Finset Pt} {G : Finset Edge}
namespace ULHC
theorem _root_.solution (hGV : Inside V G) {x y : Node} (hx : x ∈ candN V G) (hy : y ∈ candN V G) :
    gedgeCost V G x y ≤ 300 * (V.card + 1) ^ 2 := by
  obtain ⟨hx1, hxn, hxc⟩ := node_len x hx
  obtain ⟨_, hyn, _⟩ := node_len y hy
  have := cr2BCost_le hGV hx1 hxn hxc hyn
  unfold gedgeCost chainOKBCost
  nlinarith
end ULHC
