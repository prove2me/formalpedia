-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.extremePoints_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:37:28.186296+00:00
-- url     : https://prove2.me/submissions/431188b9-bcb2-4061-94e7-d290bb2a9544

module
public import Mathlib.Data.Set.Card
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
public import Theorems.Thm_PretorsionImageClosed_SetClosure_closure_extremePoints

set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution [Finite E]
    (hae : c.IsAntiExchange) (hempty : c.IsClosed ∅)
    {C : Set E} (hC : c.IsClosed C) (hCne : C.Nonempty) :
    (c.extremePoints C).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have : C = ∅ := by
    rw [← closure_extremePoints hae hC, h, hempty.closure_eq]
  exact hCne.ne_empty this
end PretorsionImageClosed.SetClosure
