-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.coe_iSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:49:22.872934+00:00
-- url     : https://prove2.me/submissions/31f47d9d-d10b-41a6-82d6-854e4238cea6

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
theorem _root_.solution {ι : Sort*} (f : ι → c.Closeds) :
    ((⨆ i, f i : c.Closeds) : Set E) = c (⋃ i, (f i : Set E)) :=
  congrArg Subtype.val (c.gi.l_iSup_u f).symm
end PretorsionImageClosed.SetClosure
