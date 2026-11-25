-- Prove2me | solution 1 for PretorsionImageClosed.imageSubobject_epi_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:12:39.313249+00:00
-- url     : https://prove2.me/submissions/907a671d-e42e-4a9b-9f20-2714e0195762

module
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C]
namespace PretorsionImageClosed
theorem _root_.solution {W X Y : C} (e : W ⟶ X) [Epi e] (f : X ⟶ Y) :
    imageSubobject (e ≫ f) = imageSubobject f := by
  rw [imageSubobject_eq_kernelSubobject_cokernel_π, imageSubobject_eq_kernelSubobject_cokernel_π f]
  have : cokernel.π (e ≫ f) = cokernel.π f ≫ (cokernelEpiComp e f).inv := by
    rw [Iso.eq_comp_inv]
    exact cokernel.π_desc _ _ _
  rw [this, kernelSubobject_comp_mono]
end PretorsionImageClosed
