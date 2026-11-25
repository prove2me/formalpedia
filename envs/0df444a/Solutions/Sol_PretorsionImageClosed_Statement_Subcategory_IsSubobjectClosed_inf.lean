-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.IsSubobjectClosed.inf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:22:22.499309+00:00
-- url     : https://prove2.me/submissions/72ec7adc-cf9e-46f2-8b67-61024f75fc6f

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
namespace IsSubobjectClosed
theorem _root_.solution {Z Z' : Subcategory C} (h : Z.IsSubobjectClosed)
    (h' : Z'.IsSubobjectClosed) : (Z ⊓ Z').IsSubobjectClosed :=
  fun f hf hY => ⟨h f hf hY.1, h' f hf hY.2⟩
end IsSubobjectClosed
end PretorsionImageClosed.Statement.Subcategory
