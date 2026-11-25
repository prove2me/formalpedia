-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.compact_isMinimalGenerator_iff_eq_extremePoints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:57:30.572149+00:00
-- url     : https://prove2.me/submissions/1194fcc3-fda2-42d0-8d37-7fdcf4cff5e3

module
public import Mathlib.Order.CompactlyGenerated.Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Theorems.Thm_PretorsionImageClosed_SetClosure_finite_minimalGenerator_eq_extremePoints
public import Theorems.Thm_PretorsionImageClosed_SetClosure_compact_extremePoints_basis

set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    {C : c.Closeds} (hcompact : IsCompactElement C) {B : Set E} :
    c.IsMinimalGenerator B (C : Set E) ↔
      B = c.extremePoints (C : Set E) := by
  constructor
  · exact finite_minimalGenerator_eq_extremePoints hfin hae C.2
  · intro hB
    rw [hB]
    exact (compact_extremePoints_basis hfin hae hcompact).2
end PretorsionImageClosed.SetClosure
