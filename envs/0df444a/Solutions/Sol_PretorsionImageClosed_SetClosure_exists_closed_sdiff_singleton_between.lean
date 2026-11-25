-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.exists_closed_sdiff_singleton_between
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:39:52.95569+00:00
-- url     : https://prove2.me/submissions/a412ed0f-51ba-4a00-a16b-6059875cc912

module
public import Mathlib.Data.Set.Card
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
public import Theorems.Thm_PretorsionImageClosed_SetClosure_exists_extreme_not_mem_of_ssubset
public import Theorems.Thm_PretorsionImageClosed_SetClosure_mem_extremePoints_iff_isClosed_sdiff_singleton


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
    ∃ x : E, x ∈ D \ C ∧ c.IsClosed (D \ {x}) ∧ C ⊆ D \ {x} := by
  obtain ⟨x, hxextreme, hxC⟩ :=
    exists_extreme_not_mem_of_ssubset hae hC hD hCD
  refine ⟨x, ⟨hxextreme.1, hxC⟩,
    (mem_extremePoints_iff_isClosed_sdiff_singleton hD hxextreme.1).1 hxextreme, ?_⟩
  intro y hyC
  exact ⟨hCD.subset hyC, by
    simpa [Set.mem_singleton_iff] using fun hyx : y = x ↦ hxC (hyx ▸ hyC)⟩
end PretorsionImageClosed.SetClosure
