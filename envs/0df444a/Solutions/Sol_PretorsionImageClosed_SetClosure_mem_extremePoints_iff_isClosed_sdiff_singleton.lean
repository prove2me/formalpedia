-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.mem_extremePoints_iff_isClosed_sdiff_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:16:08.438654+00:00
-- url     : https://prove2.me/submissions/c4b9fbac-98c2-44a8-af21-a228f26c879f

module
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Order.Closure
public import Mathlib.Order.Preorder.Finite
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
public import Theorems.Thm_PretorsionImageClosed_SetClosure_mem_extremePoints
public import Theorems.Thm_PretorsionImageClosed_SetClosure_isClosed_sdiff_singleton_of_not_mem_closure

set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed
open PretorsionImageClosed.SetClosure
variable {E : Type*} (c : SetClosure E)
variable {c}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution
    {C : Set E} {x : E} (hC : c.IsClosed C) (hxC : x ∈ C) :
    x ∈ c.extremePoints C ↔ c.IsClosed (C \ {x}) := by
  rw [mem_extremePoints, and_iff_right hxC]
  constructor
  · exact isClosed_sdiff_singleton_of_not_mem_closure hC
  · intro hdel hx
    simp [hdel.closure_eq] at hx
end PretorsionImageClosed.SetClosure
