-- Prove2me | solution 1 for TunnellMap.OrthogonalFrame.gram_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:47:56.610014+00:00
-- url     : https://prove2.me/submissions/f5d1b1af-9b55-48c7-8409-3ec2c4d636a4

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
import Theorems.Thm_TunnellMap_lagrange_identity

set_option autoImplicit true
open TunnellMap
open TunnellMap.OrthogonalFrame
variable {p : Triple} (F : OrthogonalFrame p)
namespace TunnellMap.OrthogonalFrame
theorem _root_.solution :
    dot F.e₁ F.e₁ * dot F.e₂ F.e₂ - dot F.e₁ F.e₂ ^ 2 = dot p p := by
  have h := lagrange_identity F.e₁ F.e₂
  rw [F.cross_eq] at h
  exact h.symm
end TunnellMap.OrthogonalFrame
