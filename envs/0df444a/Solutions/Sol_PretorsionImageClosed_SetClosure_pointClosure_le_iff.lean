-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.pointClosure_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:49:38.88113+00:00
-- url     : https://prove2.me/submissions/befcfbc2-f506-4607-b9ae-2f2c96c500fe

module
public import Mathlib.Order.Grade
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_ClosedSets

set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*}
variable {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution {x : E} {C : c.Closeds} :
    c.pointClosure x ≤ C ↔ x ∈ (C : Set E) := by
  change c ({x} : Set E) ⊆ (C : Set E) ↔ _
  rw [C.2.closure_le_iff, singleton_subset_iff]
end PretorsionImageClosed.SetClosure
