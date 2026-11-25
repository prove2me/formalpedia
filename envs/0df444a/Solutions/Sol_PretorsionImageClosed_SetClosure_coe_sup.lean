-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.coe_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:51:44.183799+00:00
-- url     : https://prove2.me/submissions/dac9410f-bada-45b4-a13c-48b17efcee3b

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
    ((C ⊔ D : c.Closeds) : Set E) = c ((C : Set E) ∪ (D : Set E)) :=
  rfl
end PretorsionImageClosed.SetClosure
