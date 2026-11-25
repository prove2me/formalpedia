-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.iSup_pointClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:57:05.782947+00:00
-- url     : https://prove2.me/submissions/aa97f9ca-6ac8-4918-a22b-11136599b741

module
public import Mathlib.Order.Grade
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_ClosedSets
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_pointClosure
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_bot
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_top
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_inf
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_sup
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_iSup
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_iInf
public import Theorems.Thm_PretorsionImageClosed_SetClosure_coe_sSup
attribute [local simp] PretorsionImageClosed.SetClosure.coe_pointClosure
attribute [local simp] PretorsionImageClosed.SetClosure.coe_bot
attribute [local simp] PretorsionImageClosed.SetClosure.coe_top
attribute [local simp] PretorsionImageClosed.SetClosure.coe_inf
attribute [local simp] PretorsionImageClosed.SetClosure.coe_sup
attribute [local simp] PretorsionImageClosed.SetClosure.coe_iSup
attribute [local simp] PretorsionImageClosed.SetClosure.coe_iInf
attribute [local simp] PretorsionImageClosed.SetClosure.coe_sSup

set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*}
variable {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution (C : c.Closeds) :
    (⨆ x : (C : Set E), c.pointClosure x.1) = C := by
  apply Subtype.ext
  rw [coe_iSup]
  have hunion :
      (⋃ x : (C : Set E), ({x.1} : Set E)) = (C : Set E) := by
    ext x
    simp
  change c (⨆ x : (C : Set E), c ({x.1} : Set E)) = (C : Set E)
  rw [c.closure_iSup_closure]
  change c (⋃ x : (C : Set E), ({x.1} : Set E)) = (C : Set E)
  rw [hunion, C.2.closure_eq]
end PretorsionImageClosed.SetClosure
