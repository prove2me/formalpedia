-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.closure_extremePoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:34:28.433015+00:00
-- url     : https://prove2.me/submissions/a843904c-f791-4fde-be56-066a95e6d46b

module
public import Mathlib.Data.Set.Card
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Finite
public import Theorems.Thm_PretorsionImageClosed_SetClosure_exists_isMinimalGenerator
public import Theorems.Thm_PretorsionImageClosed_SetClosure_minimalGenerator_eq_extremePoints

set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution [Finite E]
    (hae : c.IsAntiExchange) {C : Set E} (hC : c.IsClosed C) :
    c (c.extremePoints C) = C := by
  obtain ⟨B, hB⟩ := exists_isMinimalGenerator hC
  rw [← minimalGenerator_eq_extremePoints hae hC hB]
  exact hB.1
end PretorsionImageClosed.SetClosure
