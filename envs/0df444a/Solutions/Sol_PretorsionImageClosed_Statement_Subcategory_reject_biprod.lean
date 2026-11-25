-- Prove2me | solution 1 for PretorsionImageClosed.Statement.Subcategory.reject_biprod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:54:10.590932+00:00
-- url     : https://prove2.me/submissions/13dbe473-d742-4ce4-80a6-1f8bc948b85b

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_prop_cokernel_reject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_le_kernelSubobject
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_reject_arrow_comp_eq_zero
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_reject_iff
public import Theorems.Thm_P2M_PretorsionImageClosed_Subobject_factors_of_comp_cokernel___eq_zero_a7c3f47bcca4


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement PretorsionImageClosed.Statement.Subcategory
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C] [HasLength C] {T F : Subcategory C}
namespace PretorsionImageClosed.Statement.Subcategory
theorem _root_.solution (hF : F.IsSubobjectClosed) (Y₁ Y₂ : C) :
    F.reject (Y₁ ⊞ Y₂) = Subobject.mk (biprod.map (F.reject Y₁).arrow (F.reject Y₂).arrow) := by
  apply le_antisymm
  · have hG : F.prop (cokernel (F.reject Y₁).arrow ⊞ cokernel (F.reject Y₂).arrow) :=
      F.prop_biprod (F.prop_cokernel_reject Y₁) (F.prop_cokernel_reject Y₂)
    refine (reject_le_kernelSubobject hF
      (biprod.map (cokernel.π (F.reject Y₁).arrow) (cokernel.π (F.reject Y₂).arrow)) hG).trans ?_
    have hk := kernelSubobject_arrow_comp
      (biprod.map (cokernel.π (F.reject Y₁).arrow) (cokernel.π (F.reject Y₂).arrow))
    have h₁ : (F.reject Y₁).Factors ((kernelSubobject
        (biprod.map (cokernel.π (F.reject Y₁).arrow) (cokernel.π (F.reject Y₂).arrow))).arrow ≫
          biprod.fst) := by
      apply Subobject.factors_of_comp_cokernel_π_eq_zero
      rw [Category.assoc, ← biprod.map_fst, ← Category.assoc, hk, zero_comp]
    have h₂ : (F.reject Y₂).Factors ((kernelSubobject
        (biprod.map (cokernel.π (F.reject Y₁).arrow) (cokernel.π (F.reject Y₂).arrow))).arrow ≫
          biprod.snd) := by
      apply Subobject.factors_of_comp_cokernel_π_eq_zero
      rw [Category.assoc, ← biprod.map_snd, ← Category.assoc, hk, zero_comp]
    refine Subobject.le_mk_of_comm (biprod.lift ((F.reject Y₁).factorThru _ h₁)
      ((F.reject Y₂).factorThru _ h₂)) ?_
    apply biprod.hom_ext <;> simp
  · rw [le_reject_iff hF]
    intro Y g hY
    rw [← Subobject.underlyingIso_hom_comp_eq_mk, Category.assoc]
    have : biprod.map (F.reject Y₁).arrow (F.reject Y₂).arrow ≫ g = 0 := by
      apply biprod.hom_ext'
      · rw [biprod.inl_map_assoc, reject_arrow_comp_eq_zero hF _ hY, comp_zero]
      · rw [biprod.inr_map_assoc, reject_arrow_comp_eq_zero hF _ hY, comp_zero]
    rw [this, comp_zero]
end PretorsionImageClosed.Statement.Subcategory
