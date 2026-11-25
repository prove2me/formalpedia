-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.pointClosure_injective_closeds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:57:42.519665+00:00
-- url     : https://prove2.me/submissions/12609567-8a95-4695-812c-c7523484ded4

module
public import Mathlib.Order.Grade
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_ClosedSets
public import Theorems.Thm_PretorsionImageClosed_SetClosure_pointClosure_injective


set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*}
variable {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution
    (hae : c.IsAntiExchange) (hempty : c.IsClosed ∅) :
    Function.Injective c.pointClosure := by
  intro x y hxy
  apply pointClosure_injective hae hempty
  exact congrArg Subtype.val hxy
end PretorsionImageClosed.SetClosure
