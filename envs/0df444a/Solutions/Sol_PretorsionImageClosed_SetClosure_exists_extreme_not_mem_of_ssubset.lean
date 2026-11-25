-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.exists_extreme_not_mem_of_ssubset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:37:26.889032+00:00
-- url     : https://prove2.me/submissions/1fbc1ca2-0b31-4eda-9553-847806534ed1

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
    (hae : c.IsAntiExchange) {C D : Set E}
    (hC : c.IsClosed C) (hD : c.IsClosed D) (hCD : C ⊂ D) :
    ∃ x ∈ c.extremePoints D, x ∉ C := by
  by_contra h
  push Not at h
  have hextreme : c.extremePoints D ⊆ C := fun x hx ↦ h x hx
  have hDC : D ⊆ C := by
    intro x hxD
    have hxClosure : x ∈ c (c.extremePoints D) := by
      rw [closure_extremePoints hae hD]
      exact hxD
    have hx := c.monotone hextreme hxClosure
    simpa [hC.closure_eq] using hx
  exact hCD.not_subset hDC
end PretorsionImageClosed.SetClosure
