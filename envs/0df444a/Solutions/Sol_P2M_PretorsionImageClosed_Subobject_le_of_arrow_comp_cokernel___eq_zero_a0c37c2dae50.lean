-- Prove2me | solution 1 for P2M_PretorsionImageClosed_Subobject_le_of_arrow_comp_cokernel___eq_zero_a0c37c2dae50
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:45:31.672187+00:00
-- url     : https://prove2.me/submissions/7c535dba-9c09-43de-bc13-cdab236ec03f

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
theorem _root_.solution {X : C} {S L : Subobject X}
    (h : S.arrow ≫ cokernel.π L.arrow = 0) : S ≤ L :=
  (le_kernelSubobject _ _ h).trans_eq (kernelSubobject_cokernel_π_arrow L)
end Subobject
end PretorsionImageClosed
