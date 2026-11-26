-- Prove2me | solution 1 for P2M_TunnellMap_OrthogonalFrame_e__orthogonal_756a68c1a1d3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:54:05.240537+00:00
-- url     : https://prove2.me/submissions/76e1a847-e324-412d-be66-397fa9148b16

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
import Theorems.Thm_TunnellMap_dot_comm
import Theorems.Thm_TunnellMap_dot_cross_self_right

set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)
namespace TunnellMap.OrthogonalFrame
theorem _root_.solution : dot p F.e₂ = 0 := by
  have h := dot_cross_self_right F.e₁ F.e₂
  rw [F.cross_eq] at h
  calc
    dot p F.e₂ = dot F.e₂ p := dot_comm _ _
    _ = 0 := h
end TunnellMap.OrthogonalFrame
