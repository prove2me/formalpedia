-- Prove2me | solution 1 for PretorsionImageClosed.Subobject.preimage_imageSubobject_arrow_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:42:24.308775+00:00
-- url     : https://prove2.me/submissions/750623df-6b83-4110-a618-5c5f7cfe1309

module
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Theorems.Thm_PretorsionImageClosed_imageSubobject_factors_self

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C]
namespace PretorsionImageClosed
namespace Subobject
theorem _root_.solution {X Y : C} (p : X ⟶ Y) [Epi p]
    (S : Subobject X) (hS : kernelSubobject p ≤ S) :
    Subobject.preimage p (imageSubobject (S.arrow ≫ p)) = S := by
  apply le_antisymm
  · have hk : kernel.ι p ≫ cokernel.π S.arrow = 0 := by
      rw [← kernelSubobject_arrow' p, Category.assoc, ← Subobject.ofLE_arrow hS, Category.assoc,
        cokernel.condition, comp_zero, comp_zero]
    have hVe : (imageSubobject (S.arrow ≫ p)).arrow ≫ Abelian.epiDesc p _ hk = 0 := by
      rw [← cancel_epi (factorThruImageSubobject (S.arrow ≫ p)), ← Category.assoc,
        imageSubobject_arrow_comp, Category.assoc, Abelian.comp_epiDesc, cokernel.condition,
        comp_zero]
    have hzero : (Subobject.preimage p (imageSubobject (S.arrow ≫ p))).arrow ≫
        cokernel.π S.arrow = 0 := by
      rw [← Abelian.comp_epiDesc p _ hk, ← Category.assoc,
        ← Subobject.factorThru_arrow _ _ (Subobject.preimage_arrow_comp_factors p _),
        Category.assoc, hVe, comp_zero]
    exact (le_kernelSubobject _ _ hzero).trans_eq (kernelSubobject_cokernel_π_arrow S)
  · rw [Subobject.le_preimage_iff]
    exact imageSubobject_factors_self _
end Subobject
end PretorsionImageClosed
