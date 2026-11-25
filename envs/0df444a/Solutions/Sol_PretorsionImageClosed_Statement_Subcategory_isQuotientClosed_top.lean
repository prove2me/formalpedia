-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.isQuotientClosed_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:23:31.473063+00:00
-- url     : https://prove2.me/submissions/f5d2f436-6e36-4b9b-9e08-0631d2864613

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
theorem _root_.solution : (⊤ : Subcategory C).IsQuotientClosed := fun _ _ _ => trivial
end PretorsionImageClosed.Statement.Subcategory
