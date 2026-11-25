-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.reject_arrow_comp_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:59:51.201447+00:00
-- url     : https://prove2.me/submissions/c055ddbc-a0fd-4c31-ac5b-887608b95a69

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_le_kernelSubobject

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement ZeroObject
variable {C : Type*} [Category C] [Abelian C]
open PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
variable (T : Subcategory C) (X : C)
variable (F : Subcategory C)
variable [HasLength C]
variable {T X}
variable (X)
variable {F X}
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution (hF : F.IsSubobjectClosed) {Y : C} (g : X ⟶ Y) (hY : F.prop Y) :
    (F.reject X).arrow ≫ g = 0 := by
  rw [← Subobject.ofLE_arrow (reject_le_kernelSubobject hF g hY), Category.assoc,
    kernelSubobject_arrow_comp, comp_zero]
end PretorsionImageClosed.Statement.Subcategory
