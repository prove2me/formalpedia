-- Prove2me | solution 1 for P2M_TunnellMap_OrthogonalFrame_e__orthogonal_6c82c70f8b3a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:54:04.430818+00:00
-- url     : https://prove2.me/submissions/f3bf7627-8127-45c4-aab9-05ac569d81ca

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
import Theorems.Thm_TunnellMap_dot_comm
import Theorems.Thm_TunnellMap_dot_cross_self_left

set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)
namespace TunnellMap.OrthogonalFrame
theorem _root_.solution : dot p F.e₁ = 0 := by
  have h := dot_cross_self_left F.e₁ F.e₂
  rw [F.cross_eq] at h
  calc
    dot p F.e₁ = dot F.e₁ p := dot_comm _ _
    _ = 0 := h
end TunnellMap.OrthogonalFrame
