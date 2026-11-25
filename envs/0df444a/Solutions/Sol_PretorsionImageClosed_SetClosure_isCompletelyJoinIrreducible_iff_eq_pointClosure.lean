-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.isCompletelyJoinIrreducible_iff_eq_pointClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:56:29.306357+00:00
-- url     : https://prove2.me/submissions/24860725-c7b1-4022-af5b-7ec50a9110d7

module
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_ClosedSets
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible
public import Theorems.Thm_PretorsionImageClosed_SetClosure_pointClosure_isCompletelyJoinIrreducible
public import Theorems.Thm_PretorsionImageClosed_SetClosure_iSup_pointClosure
public import Theorems.Thm_PretorsionImageClosed_SetClosure_pointClosure_le_iff


set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed
open PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    (hempty : c.IsClosed ∅) (J : c.Closeds) :
    IsCompletelyJoinIrreducible J ↔
      ∃ x : E, J = c.pointClosure x := by
  constructor
  · intro hJ
    let P : Set c.Closeds :=
      c.pointClosure '' (J : Set E)
    have hsup : sSup P = J := by
      apply le_antisymm
      · apply sSup_le
        intro K hK
        obtain ⟨x, hxJ, rfl⟩ := hK
        exact pointClosure_le_iff.2 hxJ
      · rw [← iSup_pointClosure J]
        apply iSup_le
        intro x
        exact le_sSup ⟨x.1, x.2, rfl⟩
    have hmem : J ∈ P := hJ P hsup
    obtain ⟨x, hxJ, hx⟩ := hmem
    exact ⟨x, hx.symm⟩
  · rintro ⟨x, rfl⟩
    exact pointClosure_isCompletelyJoinIrreducible hfin hae hempty x
end PretorsionImageClosed.SetClosure
