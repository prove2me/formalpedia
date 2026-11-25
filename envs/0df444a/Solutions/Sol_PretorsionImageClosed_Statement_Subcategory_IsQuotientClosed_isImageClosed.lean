-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.IsQuotientClosed.isImageClosed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:15:30.492897+00:00
-- url     : https://prove2.me/submissions/3460609c-95f7-440c-a11f-aa41ea992fc2

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
namespace IsQuotientClosed
theorem _root_.solution {Z : Subcategory A} (h : Z.IsQuotientClosed) :
    Z.IsImageClosed := fun f hX _ =>
  h (factorThruImage f) inferInstance hX
end IsQuotientClosed
end PretorsionImageClosed.Statement.Subcategory
