-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.reject_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:13.910469+00:00
-- url     : https://prove2.me/submissions/8c856053-e221-4e3f-b080-9d03c019296d

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_reject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_le
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_arrow_comp_eq_zero
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_reject_iff

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C] [HasLength C] {T F : Subcategory C}
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution (hF : F.IsSubobjectClosed) {X Y : C} (e : X ≅ Y) :
    F.reject Y = Subobject.mk ((F.reject X).arrow ≫ e.hom) := by
  apply le_antisymm
  · apply reject_le hF
    refine F.prop_of_iso ?_ (F.prop_cokernel_reject X)
    exact (cokernelCompIsIso (F.reject X).arrow e.hom).symm ≪≫
      cokernelIsoOfEq (Subobject.underlyingIso_arrow _).symm ≪≫ cokernelEpiComp _ _
  · rw [le_reject_iff hF]
    intro W g hW
    rw [← cancel_epi (Subobject.underlyingIso ((F.reject X).arrow ≫ e.hom)).inv, comp_zero,
      ← Category.assoc, Subobject.underlyingIso_arrow, Category.assoc,
      reject_arrow_comp_eq_zero hF (e.hom ≫ g) hW]
end PretorsionImageClosed.Statement.Subcategory
