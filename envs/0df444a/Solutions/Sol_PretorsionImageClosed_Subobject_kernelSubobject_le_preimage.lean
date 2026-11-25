-- Prove2me | solution 1 for PretorsionImageClosed.Subobject.kernelSubobject_le_preimage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:21:12.139031+00:00
-- url     : https://prove2.me/submissions/027079a3-8794-4833-908e-e3fa0c871755

module
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Theorems.Thm_PretorsionImageClosed_Subobject_factors_zero

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
theorem _root_.solution {X Y : C} (p : X ⟶ Y) (U : Subobject Y) :
    kernelSubobject p ≤ Subobject.preimage p U := by
  rw [Subobject.le_preimage_iff, kernelSubobject_arrow_comp]
  exact Subobject.factors_zero U
end Subobject
end PretorsionImageClosed
