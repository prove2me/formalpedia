-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.inf_prop_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:48:45.977613+00:00
-- url     : https://prove2.me/submissions/18f87354-a346-4384-afbd-b39a02665fd0

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
theorem _root_.solution (Z Z' : Subcategory C) (X : C) :
    (Z ⊓ Z').prop X ↔ Z.prop X ∧ Z'.prop X := Iff.rfl
end PretorsionImageClosed.Statement.Subcategory
