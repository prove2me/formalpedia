-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.IsImageClosed.iInf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:35:05.588377+00:00
-- url     : https://prove2.me/submissions/d627c33a-c5c4-4404-b0d7-7cc47339a957

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
namespace IsImageClosed
theorem _root_.solution {ι : Sort*} {Z : ι → Subcategory A} (h : ∀ i, (Z i).IsImageClosed) :
    (Subcategory.iInf Z).IsImageClosed := by
  intro X Y f hX hY
  rw [iInf_prop_iff] at hX hY ⊢
  exact fun i => h i f (hX i) (hY i)
end IsImageClosed
end PretorsionImageClosed.Statement.Subcategory
