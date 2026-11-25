-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.isSubobjectClosed_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:21:37.388711+00:00
-- url     : https://prove2.me/submissions/bcd44fdb-df4e-438e-8a30-c27c245d9b2e

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
theorem _root_.solution : (⊤ : Subcategory C).IsSubobjectClosed := fun _ _ _ => trivial
end PretorsionImageClosed.Statement.Subcategory
