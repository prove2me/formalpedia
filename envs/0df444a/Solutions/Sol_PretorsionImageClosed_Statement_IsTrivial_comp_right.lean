-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsTrivial.comp_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:57:28.172012+00:00
-- url     : https://prove2.me/submissions/86388e3c-6f85-46d0-8bb6-6ee5480aa6a7

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
open PretorsionImageClosed.Statement
variable {C : Type*} [Category C] {Z : ObjectProperty C}
namespace PretorsionImageClosed.Statement
namespace IsTrivial
theorem _root_.solution {X Y W : C} {f : X ⟶ Y} (h : IsTrivial Z f) (g : Y ⟶ W) :
    IsTrivial Z (f ≫ g) := by
  obtain ⟨V, hV, a, b, rfl⟩ := h
  exact ⟨V, hV, a, b ≫ g, by simp⟩
end IsTrivial
end PretorsionImageClosed.Statement
