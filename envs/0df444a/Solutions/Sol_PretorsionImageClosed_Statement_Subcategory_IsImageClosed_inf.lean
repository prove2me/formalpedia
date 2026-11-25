-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.IsImageClosed.inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:22:33.37774+00:00
-- url     : https://prove2.me/submissions/5ebc963f-8f6e-4568-b9d2-36ecaad5b050

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
theorem _root_.solution {Z Z' : Subcategory A} (h : Z.IsImageClosed) (h' : Z'.IsImageClosed) :
    (Z ⊓ Z').IsImageClosed := fun f hX hY => ⟨h f hX.1 hY.1, h' f hX.2 hY.2⟩
end IsImageClosed
end PretorsionImageClosed.Statement.Subcategory
