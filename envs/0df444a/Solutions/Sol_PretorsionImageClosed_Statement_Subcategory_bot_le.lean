-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.bot_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:52:58.346941+00:00
-- url     : https://prove2.me/submissions/bc450a7f-0211-43a3-9118-528605f825ca

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
theorem _root_.solution (Z : Subcategory C) : ⊥ ≤ Z := fun _ h => Z.prop_of_isZero h
end PretorsionImageClosed.Statement.Subcategory
