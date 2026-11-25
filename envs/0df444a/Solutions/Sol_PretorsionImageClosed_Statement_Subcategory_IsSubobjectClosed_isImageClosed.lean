-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.IsSubobjectClosed.isImageClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:15:36.625129+00:00
-- url     : https://prove2.me/submissions/62963fb5-e483-4bdb-a280-86ec2dd335b0

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
namespace IsSubobjectClosed
theorem _root_.solution {Z : Subcategory A} (h : Z.IsSubobjectClosed) :
    Z.IsImageClosed := fun f _ hY =>
  h (image.ι f) inferInstance hY
end IsSubobjectClosed
end PretorsionImageClosed.Statement.Subcategory
