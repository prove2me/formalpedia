-- Prove2me | solution 1 for PretorsionImageClosed.Subobject.mk_ofLE_mk_comp_arrow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:45:42.664105+00:00
-- url     : https://prove2.me/submissions/8f785142-a759-4f51-b9ba-7aaa18605178

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
theorem _root_.solution {X : C} (S : Subobject X) (K : Subobject (S : C)) :
    Subobject.mk (Subobject.ofLE _ S (Subobject.mk_comp_arrow_le S K)) = K := by
  conv_rhs => rw [← Subobject.mk_arrow K]
  apply Subobject.mk_eq_mk_of_comm _ _ (Subobject.underlyingIso (K.arrow ≫ S.arrow))
  rw [← cancel_mono S.arrow, Category.assoc, Subobject.ofLE_arrow,
    Subobject.underlyingIso_hom_comp_eq_mk]
end Subobject
end PretorsionImageClosed
