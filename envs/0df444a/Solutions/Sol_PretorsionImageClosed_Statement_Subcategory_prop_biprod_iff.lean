-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.prop_biprod_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:47:12.893026+00:00
-- url     : https://prove2.me/submissions/4bc569e2-2b15-419b-a6fd-bbe81e99e65c

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_biprod_left
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_biprod_right

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
theorem _root_.solution {X Y : C} : Z.prop (X ⊞ Y) ↔ Z.prop X ∧ Z.prop Y :=
  ⟨fun h => ⟨Z.prop_biprod_left h, Z.prop_biprod_right h⟩, fun h => Z.prop_biprod h.1 h.2⟩
end PretorsionImageClosed.Statement.Subcategory
