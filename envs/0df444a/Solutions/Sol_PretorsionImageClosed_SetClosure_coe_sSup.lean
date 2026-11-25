-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.coe_sSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:52:04.093662+00:00
-- url     : https://prove2.me/submissions/873522d7-b786-4c4d-9178-3d39ee224a5a

module
public import Mathlib.Order.Grade
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_ClosedSets
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_iSup
attribute [local simp] PretorsionImageClosed.SetClosure.coe_iSup

set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*}
variable {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution (S : Set c.Closeds) :
    ((sSup S : c.Closeds) : Set E) =
      c (⋃ C : S, (C.1 : Set E)) := by
  rw [sSup_eq_iSup' S, coe_iSup]
end PretorsionImageClosed.SetClosure
