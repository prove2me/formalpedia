-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsTrivial.of_prop_tgt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:46:15.938146+00:00
-- url     : https://prove2.me/submissions/586265eb-e079-4d01-8af7-64b7a1cd88aa

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
theorem _root_.solution {X Y : C} (f : X ⟶ Y) (hY : Z Y) : IsTrivial Z f :=
  ⟨Y, hY, f, 𝟙 Y, Category.comp_id f⟩
end IsTrivial
end PretorsionImageClosed.Statement
