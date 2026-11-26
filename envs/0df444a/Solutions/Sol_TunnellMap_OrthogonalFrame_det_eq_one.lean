-- Prove2me | solution 1 for TunnellMap.OrthogonalFrame.det_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:44:38.352054+00:00
-- url     : https://prove2.me/submissions/c06208d0-0eb0-45dc-9ccc-2c634fe09514

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice

set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)
namespace TunnellMap.OrthogonalFrame
theorem _root_.solution : det3 F.e₁ F.e₂ F.z = 1 := by
  rw [det3, F.cross_eq]
  exact F.bezout
end TunnellMap.OrthogonalFrame
