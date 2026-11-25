-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.coe_inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:51:40.444733+00:00
-- url     : https://prove2.me/submissions/beab49fb-300f-4427-aacc-3ccd8a75f057

module
public import Mathlib.Order.Grade
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_ClosedSets

set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*}
variable {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution (C D : c.Closeds) :
    ((C ⊓ D : c.Closeds) : Set E) = (C : Set E) ∩ (D : Set E) :=
  rfl
end PretorsionImageClosed.SetClosure
