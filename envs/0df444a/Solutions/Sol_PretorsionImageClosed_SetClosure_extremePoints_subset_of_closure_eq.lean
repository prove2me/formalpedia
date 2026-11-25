-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.extremePoints_subset_of_closure_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:17:50.667924+00:00
-- url     : https://prove2.me/submissions/d641de69-5cfc-4fbf-96a0-d0b7b9ec5a8d

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
    {B C : Set E} (hBC : c B = C) :
    c.extremePoints C ⊆ B := by
  intro x hx
  by_contra hxB
  have hBsub : B ⊆ C \ {x} := by
    intro y hyB
    refine ⟨?_, ?_⟩
    · exact hBC ▸ c.le_closure B hyB
    · simpa [Set.mem_singleton_iff] using fun hyx : y = x ↦ hxB (hyx ▸ hyB)
  exact hx.2 (c.monotone hBsub (hBC ▸ hx.1))
end PretorsionImageClosed.SetClosure
