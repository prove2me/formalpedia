-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.compact_extremePoints_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:31:02.36072+00:00
-- url     : https://prove2.me/submissions/9b128dc8-8b68-4e97-a437-c66139ed89db

module
public import Mathlib.Order.CompactlyGenerated.Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Theorems.Thm_PretorsionImageClosed_SetClosure_exists_finite_generator_of_isCompactElement
public import Theorems.Thm_PretorsionImageClosed_SetClosure_exists_finite_isMinimalGenerator
public import Theorems.Thm_PretorsionImageClosed_SetClosure_finite_minimalGenerator_eq_extremePoints

set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution
    (hfin : c.IsFinitary) (hae : c.IsAntiExchange)
    {C : c.Closeds} (hcompact : IsCompactElement C) :
    (c.extremePoints (C : Set E)).Finite ∧
      c.IsMinimalGenerator (c.extremePoints (C : Set E)) (C : Set E) := by
  obtain ⟨B, hBfin, -, hBC⟩ :=
    exists_finite_generator_of_isCompactElement hcompact
  obtain ⟨B₀, hB₀fin, -, hB₀⟩ :=
    exists_finite_isMinimalGenerator hBfin hBC
  have hEq :=
    finite_minimalGenerator_eq_extremePoints hfin hae C.2 hB₀
  constructor
  · exact hEq ▸ hB₀fin
  · exact hEq ▸ hB₀
end PretorsionImageClosed.SetClosure
