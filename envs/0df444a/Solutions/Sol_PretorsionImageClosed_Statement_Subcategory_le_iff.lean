-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:44:20.830724+00:00
-- url     : https://prove2.me/submissions/1a11ee85-8d2f-43cd-8f41-219ad7ce3213

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
theorem _root_.solution {Z Z' : Subcategory C} : Z ≤ Z' ↔ ∀ X, Z.prop X → Z'.prop X := Iff.rfl
end PretorsionImageClosed.Statement.Subcategory
