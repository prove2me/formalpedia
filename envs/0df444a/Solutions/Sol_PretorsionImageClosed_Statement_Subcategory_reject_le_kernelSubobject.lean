-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.reject_le_kernelSubobject
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:57:44.797286+00:00
-- url     : https://prove2.me/submissions/02d731fe-ab0b-4646-a494-ae7bef2027c4

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_kernelSubobject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_le

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
    F.reject X ≤ kernelSubobject g :=
  reject_le hF (prop_cokernel_kernelSubobject hF g hY)
end PretorsionImageClosed.Statement.Subcategory
