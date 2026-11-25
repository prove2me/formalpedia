-- Prove2me | solution 1 for PretorsionImageClosed.Subobject.preimage_factors_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:40:47.223839+00:00
-- url     : https://prove2.me/submissions/ad5e6824-6629-4c75-bb80-bd57880a308f

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
namespace Subobject
theorem _root_.solution {X Y W : C} (p : X ⟶ Y) (U : Subobject Y) (f : W ⟶ X) :
    (Subobject.preimage p U).Factors f ↔ U.Factors (f ≫ p) := by
  rw [kernelSubobject_factors_iff, ← Category.assoc,
    ← kernelSubobject_factors_iff, kernelSubobject_cokernel_π_arrow]
end Subobject
end PretorsionImageClosed
