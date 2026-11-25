-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.coe_iInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:51:51.289672+00:00
-- url     : https://prove2.me/submissions/7d00bd3f-2ea3-4aff-93b4-ee5fac6bad4c

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
    ((⨅ i, f i : c.Closeds) : Set E) = ⋂ i, (f i : Set E) :=
  c.gi.gc.u_iInf
end PretorsionImageClosed.SetClosure
