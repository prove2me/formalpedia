-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.isClosed_sdiff_singleton_of_not_mem_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:10:48.522215+00:00
-- url     : https://prove2.me/submissions/e152bd96-a9a2-4fbf-8e30-35dfdc123632

module
public import Mathlib.Data.Set.Finite.Powerset
public import Mathlib.Order.Closure
public import Mathlib.Order.Preorder.Finite
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic

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
    {C : Set E} {x : E} (hC : c.IsClosed C)
    (hx : x ∉ c (C \ {x})) :
    c.IsClosed (C \ {x}) := by
  rw [ClosureOperator.isClosed_iff_closure_le]
  intro y hy
  exact ⟨c.closure_min sdiff_subset hC hy, fun hyx ↦ hx (hyx ▸ hy)⟩
end PretorsionImageClosed.SetClosure
