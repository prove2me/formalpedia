-- Prove2me | solution 1 for PretorsionImageClosed.SetClosure.isCompactElement_iff_exists_finite_generator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:57:11.205507+00:00
-- url     : https://prove2.me/submissions/d1499d7e-e930-4c99-9a5f-d741f0699997

module
public import Mathlib.Order.CompactlyGenerated.Basic
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_CompletelyJoinIrreducible
public import Definitions.Def_PretorsionImageClosed_ConvexGeometry_Compact
public import Theorems.Thm_PretorsionImageClosed_SetClosure_finiteClosure_isCompactElement
public import Theorems.Thm_PretorsionImageClosed_SetClosure_exists_finite_generator_of_isCompactElement

set_option autoImplicit true
@[expose] public section
public section
open Set
open PretorsionImageClosed PretorsionImageClosed.SetClosure
variable {E : Type*} {c : SetClosure E}
namespace PretorsionImageClosed.SetClosure
theorem _root_.solution
    (hfin : c.IsFinitary) {C : c.Closeds} :
    IsCompactElement C ↔
      ∃ B : Set E, B.Finite ∧ B ⊆ (C : Set E) ∧
        c B = (C : Set E) := by
  constructor
  · exact exists_finite_generator_of_isCompactElement
  · rintro ⟨B, hBfin, -, hBC⟩
    have hcompact : IsCompactElement (c.toCloseds B) :=
      finiteClosure_isCompactElement hfin hBfin
    have hEq : c.toCloseds B = C :=
      Subtype.ext hBC
    exact hEq ▸ hcompact
end PretorsionImageClosed.SetClosure
