-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.isImageClosed_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:48:46.834896+00:00
-- url     : https://prove2.me/submissions/ad39f9cf-33fe-49a7-9066-8a444e8be50c

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
variable {A : Type*} [Category A] [Abelian A]
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (Z : Subcategory A)
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution : (⊤ : Subcategory A).IsImageClosed := fun _ _ _ => trivial
end PretorsionImageClosed.Statement.Subcategory
