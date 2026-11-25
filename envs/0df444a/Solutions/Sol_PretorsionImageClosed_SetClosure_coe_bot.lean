-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.coe_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:49:51.203501+00:00
-- url     : https://prove2.me/submissions/c49fd20c-122a-45cd-a451-268af03e12cc

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
    ((⊥ : c.Closeds) : Set E) = c ∅ :=
  rfl
end PretorsionImageClosed.SetClosure
