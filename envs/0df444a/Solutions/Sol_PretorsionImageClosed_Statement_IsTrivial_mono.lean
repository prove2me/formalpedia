-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsTrivial.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:39:14.521014+00:00
-- url     : https://prove2.me/submissions/3de8aa22-d875-4aae-a42e-d1c192a2a0f8

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
theorem _root_.solution {Z' : ObjectProperty C} (hZ : Z ≤ Z') {X Y : C} {f : X ⟶ Y}
    (h : IsTrivial Z f) : IsTrivial Z' f := by
  obtain ⟨V, hV, a, b, rfl⟩ := h
  exact ⟨V, hZ V hV, a, b, rfl⟩
end IsTrivial
end PretorsionImageClosed.Statement
