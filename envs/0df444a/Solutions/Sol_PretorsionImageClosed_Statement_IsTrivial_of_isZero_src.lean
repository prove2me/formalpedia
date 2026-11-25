-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsTrivial.of_isZero_src
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:50:11.763442+00:00
-- url     : https://prove2.me/submissions/1891bcb1-29f6-4a16-a912-01e9b8c53474

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_of_prop_src

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
open PretorsionImageClosed.Statement
namespace PretorsionImageClosed.Statement
namespace IsTrivial
theorem _root_.solution {X Y : C} (f : X ⟶ Y) (hX : IsZero X) (Zs : Subcategory C) :
    IsTrivial Zs.prop f :=
  IsTrivial.of_prop_src f (Zs.prop_of_isZero hX)
end IsTrivial
end PretorsionImageClosed.Statement
