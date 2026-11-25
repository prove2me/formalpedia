-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.push_reject_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:54:22.338485+00:00
-- url     : https://prove2.me/submissions/b26770b4-ef39-4e27-95b2-092af5654f95

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_arrow_comp_eq_zero
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_reject_iff
public import Theorems.Thm_PretorsionImageClosed_Subobject_push_arrow


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C] [HasLength C] {T F : Subcategory C}
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution (hF : F.IsSubobjectClosed) {X : C} (W : Subobject X) :
    Subobject.push W (F.reject (W : C)) ≤ F.reject X := by
  rw [le_reject_iff hF]
  intro Y g hY
  rw [Subobject.push_arrow, Category.assoc, Category.assoc,
    reject_arrow_comp_eq_zero hF (W.arrow ≫ g) hY, comp_zero]
end PretorsionImageClosed.Statement.Subcategory
