-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.isCompactlyGenerated_closeds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:57:06.852474+00:00
-- url     : https://prove2.me/submissions/130b00d0-cca0-4849-96cb-c7c6f8e12700

module
public import Mathlib.Order.CompactlyGenerated.Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Theorems.Thm_PretorsionImageClosed_SetClosure_pointClosure_isCompactElement
public import Theorems.Thm_PretorsionImageClosed_SetClosure_iSup_pointClosure
public import Theorems.Thm_PretorsionImageClosed_SetClosure_pointClosure_le_iff


set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution
    (hfin : c.IsFinitary) :
    IsCompactlyGenerated c.Closeds := by
  constructor
  intro C
  let P : Set c.Closeds :=
    c.pointClosure '' (C : Set E)
  refine ⟨P, ?_, ?_⟩
  · intro J hJ
    obtain ⟨x, -, rfl⟩ := hJ
    exact pointClosure_isCompactElement hfin x
  · apply le_antisymm
    · apply sSup_le
      intro J hJ
      obtain ⟨x, hxC, rfl⟩ := hJ
      exact pointClosure_le_iff.2 hxC
    · rw [← iSup_pointClosure C]
      apply iSup_le
      intro x
      exact le_sSup ⟨x.1, x.2, rfl⟩
end PretorsionImageClosed.SetClosure
