-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.le_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:39:15.876902+00:00
-- url     : https://prove2.me/submissions/7565e333-f46c-42ba-9dab-8bed7807e722

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
theorem _root_.solution {Z Z' : Subcategory C} : Z ≤ Z' ↔ Z.prop ≤ Z'.prop := Iff.rfl
end PretorsionImageClosed.Statement.Subcategory
