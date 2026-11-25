-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.prop_iff_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:00:10.56484+00:00
-- url     : https://prove2.me/submissions/c47e5352-b1ae-49d0-bcca-dfd06f5c6290

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
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (Z : Subcategory C)
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution {X Y : C} (e : X ≅ Y) : Z.prop X ↔ Z.prop Y :=
  ⟨Z.prop_of_iso e, Z.prop_of_iso e.symm⟩
end PretorsionImageClosed.Statement.Subcategory
