-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.IsQuotientClosed.inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:23:35.044174+00:00
-- url     : https://prove2.me/submissions/06203726-a341-427a-9819-ac35ae31054d

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
namespace IsQuotientClosed
theorem _root_.solution {Z Z' : Subcategory C} (h : Z.IsQuotientClosed)
    (h' : Z'.IsQuotientClosed) : (Z ⊓ Z').IsQuotientClosed :=
  fun f hf hX => ⟨h f hf hX.1, h' f hf hX.2⟩
end IsQuotientClosed
end PretorsionImageClosed.Statement.Subcategory
