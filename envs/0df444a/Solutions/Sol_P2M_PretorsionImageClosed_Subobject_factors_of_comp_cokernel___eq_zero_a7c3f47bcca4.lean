-- Prove2me | solution 1 for P2M_PretorsionImageClosed_Subobject_factors_of_comp_cokernel___eq_zero_a7c3f47bcca4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:12:30.702772+00:00
-- url     : https://prove2.me/submissions/aaa8795e-ce39-48a5-9ac3-8bb0b8a48235

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
theorem _root_.solution {X W : C} (L : Subobject X) (f : W ⟶ X)
    (h : f ≫ cokernel.π L.arrow = 0) : L.Factors f := by
  rw [← kernelSubobject_cokernel_π_arrow L]
  exact kernelSubobject_factors _ _ h
end Subobject
end PretorsionImageClosed
