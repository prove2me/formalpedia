-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isTrivial_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:50:01.789415+00:00
-- url     : https://prove2.me/submissions/44e7be03-c8fc-486e-a621-72ee40a62232

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_zero

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]
open PretorsionImageClosed.Statement
namespace PretorsionImageClosed.Statement
theorem _root_.solution [HasZeroObject C] (Zs : Subcategory C) {X Y : C} :
    IsTrivial Zs.prop (0 : X ⟶ Y) :=
  ⟨0, Zs.prop_zero, 0, 0, by simp⟩
end PretorsionImageClosed.Statement
