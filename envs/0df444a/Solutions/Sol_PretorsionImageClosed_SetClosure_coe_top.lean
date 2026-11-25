-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.coe_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:51:36.333003+00:00
-- url     : https://prove2.me/submissions/7326f5e5-a6dd-4c81-b2d7-54ebed5cac6c

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
theorem _root_.solution (c : SetClosure E) :
    ((⊤ : c.Closeds) : Set E) = Set.univ :=
  rfl
end PretorsionImageClosed.SetClosure
