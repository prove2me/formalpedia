-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.prop_cokernel_kernelSubobject
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:44:13.215293+00:00
-- url     : https://prove2.me/submissions/b563dca7-0273-47e5-891f-42af7cb7bc2d

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace

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
variable {F X}
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution (hF : F.IsSubobjectClosed) {Y : C} (g : X ⟶ Y)
    (hY : F.prop Y) : F.prop (cokernel (kernelSubobject g).arrow) := by
  have hexact : (ShortComplex.mk (kernelSubobject g).arrow g (kernelSubobject_arrow_comp g)).Exact := by
    rw [ShortComplex.exact_iff_image_eq_kernel]
    change imageSubobject (kernelSubobject g).arrow = kernelSubobject g
    rw [imageSubobject_mono, Subobject.mk_arrow]
  exact hF _ hexact.mono_cokernelDesc hY
end PretorsionImageClosed.Statement.Subcategory
