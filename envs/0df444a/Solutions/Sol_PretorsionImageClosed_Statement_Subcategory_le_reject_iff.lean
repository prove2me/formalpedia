-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.le_reject_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:28.305135+00:00
-- url     : https://prove2.me/submissions/2121974b-b7cd-44f3-b02a-0bfdbca086c3

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_reject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_arrow_comp_eq_zero

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
theorem _root_.solution (hF : F.IsSubobjectClosed) {K : Subobject X} :
    K ≤ F.reject X ↔ ∀ {Y : C} (g : X ⟶ Y), F.prop Y → K.arrow ≫ g = 0 := by
  constructor
  · intro h Y g hY
    rw [← Subobject.ofLE_arrow h, Category.assoc, reject_arrow_comp_eq_zero hF g hY, comp_zero]
  · intro h
    have := h (cokernel.π (F.reject X).arrow) (F.prop_cokernel_reject X)
    have hle : K ≤ kernelSubobject (cokernel.π (F.reject X).arrow) := le_kernelSubobject _ _ this
    rwa [← (ShortComplex.exact_iff_image_eq_kernel _).1 (ShortComplex.exact_cokernel (F.reject X).arrow),
      imageSubobject_mono, Subobject.mk_arrow] at hle
end PretorsionImageClosed.Statement.Subcategory
