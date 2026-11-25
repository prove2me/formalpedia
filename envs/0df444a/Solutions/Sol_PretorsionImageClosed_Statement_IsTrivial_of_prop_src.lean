-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsTrivial.of_prop_src
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:44:13.74592+00:00
-- url     : https://prove2.me/submissions/f882cab9-f5f3-41c8-ad1b-f39cf38c9f8c

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
theorem _root_.solution {X Y : C} (f : X ⟶ Y) (hX : Z X) : IsTrivial Z f :=
  ⟨X, hX, 𝟙 X, f, Category.id_comp f⟩
end IsTrivial
end PretorsionImageClosed.Statement
