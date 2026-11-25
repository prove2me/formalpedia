-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.IsImageClosed.inf_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:22:27.861027+00:00
-- url     : https://prove2.me/submissions/be0cef39-eeac-451a-bfa8-65ba71a2a54a

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
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
namespace IsImageClosed
theorem _root_.solution {T F : Subcategory A} (hT : T.IsQuotientClosed)
    (hF : F.IsSubobjectClosed) : (T ⊓ F).IsImageClosed := fun f hX hY =>
  ⟨hT.isImageClosed f hX.1 hY.1, hF.isImageClosed f hX.2 hY.2⟩
end IsImageClosed
end PretorsionImageClosed.Statement.Subcategory
