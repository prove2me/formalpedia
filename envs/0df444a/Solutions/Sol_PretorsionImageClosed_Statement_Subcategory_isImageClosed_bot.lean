-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.isImageClosed_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:49:39.575358+00:00
-- url     : https://prove2.me/submissions/fd8fcbba-5b36-4f79-9d46-b0c4d6a0e7c4

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_isQuotientClosed_bot
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsQuotientClosed_isImageClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsSubobjectClosed_isImageClosed

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
variable {A : Type*} [Category A] [Abelian A]
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (Z : Subcategory A)
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution : (⊥ : Subcategory A).IsImageClosed :=
  Subcategory.isQuotientClosed_bot.isImageClosed
end PretorsionImageClosed.Statement.Subcategory
