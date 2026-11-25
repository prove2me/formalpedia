-- Prove2me | solution 1 for P2M_PretorsionImageClosed_Subobject_kernelSubobject_arrow_comp_cokernel___push_f45f7adb5033
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:20:14.716661+00:00
-- url     : https://prove2.me/submissions/d00888fc-8604-4ce8-85ba-cc9bb4a4c694

module
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Theorems.Thm_P2M_PretorsionImageClosed_Subobject_factors_of_comp_cokernel___eq_zero_a7c3f47bcca4
public import Theorems.Thm_PretorsionImageClosed_Subobject_underlyingIso_inv_comp_push_arrow
public import Theorems.Thm_PretorsionImageClosed_Subobject_push_arrow
attribute [reassoc (attr := simp)] PretorsionImageClosed.Subobject.underlyingIso_inv_comp_push_arrow

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C]
variable {C : Type*} [Category C] [Abelian C] {X : C} (S : Subobject X) (K : Subobject (S : C))
namespace PretorsionImageClosed
namespace Subobject
theorem _root_.solution :
    kernelSubobject (S.arrow ≫ cokernel.π (Subobject.push S K).arrow) = K := by
  apply le_antisymm
  · have hfac : (Subobject.push S K).Factors
        ((kernelSubobject (S.arrow ≫ cokernel.π (Subobject.push S K).arrow)).arrow ≫ S.arrow) :=
      Subobject.factors_of_comp_cokernel_π_eq_zero _ _
        (by rw [Category.assoc, kernelSubobject_arrow_comp])
    have hw := Subobject.factorThru_arrow _ _ hfac
    conv_rhs => rw [← Subobject.mk_arrow K]
    refine Subobject.le_mk_of_comm (Subobject.factorThru _ _ hfac ≫
      (Subobject.underlyingIso (K.arrow ≫ S.arrow)).hom) ?_
    rw [← cancel_mono S.arrow, Category.assoc, Category.assoc, ← Subobject.push_arrow, hw]
  · exact le_kernelSubobject _ _ (by
      rw [← Category.assoc, ← Subobject.underlyingIso_inv_comp_push_arrow S K, Category.assoc,
        cokernel.condition, comp_zero])
end Subobject
end PretorsionImageClosed
