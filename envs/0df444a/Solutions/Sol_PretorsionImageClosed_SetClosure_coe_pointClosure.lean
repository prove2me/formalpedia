-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.coe_pointClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:49:47.781797+00:00
-- url     : https://prove2.me/submissions/66a34fe9-a393-4431-b9c1-359020166b39

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
theorem _root_.solution (c : SetClosure E) (x : E) :
    (c.pointClosure x : Set E) = c ({x} : Set E) :=
  rfl
end PretorsionImageClosed.SetClosure
