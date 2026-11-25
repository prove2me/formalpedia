-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.isSpatial_closeds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:56:38.416354+00:00
-- url     : https://prove2.me/submissions/e827bc4b-b205-4f7d-8c43-13c5bf556246

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
    (hempty : c.IsClosed ∅) :
    IsSpatial c.Closeds := by
  intro C
  apply le_antisymm
  · apply sSup_le
    intro J hJ
    exact hJ.2
  · calc
      C = ⨆ x : (C : Set E), c.pointClosure x.1 :=
        (iSup_pointClosure C).symm
      _ ≤ sSup {J : c.Closeds |
          IsCompletelyJoinIrreducible J ∧ J ≤ C} := by
        apply iSup_le
        intro x
        apply le_sSup
        exact ⟨pointClosure_isCompletelyJoinIrreducible hfin hae hempty x.1,
          pointClosure_le_iff.2 x.2⟩
end PretorsionImageClosed.SetClosure
