-- Prove2me | solution 1 for PretorsionImageClosed.Subobject.mk_ofLE_push
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:19:58.754178+00:00
-- url     : https://prove2.me/submissions/e04df152-c5c8-4f58-8336-8744c158d142

module
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Theorems.Thm_PretorsionImageClosed_Subobject_push_arrow

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
    Subobject.mk (Subobject.ofLE _ S (Subobject.push_le S K)) = K := by
  conv_rhs => rw [← Subobject.mk_arrow K]
  apply Subobject.mk_eq_mk_of_comm _ _ (Subobject.underlyingIso (K.arrow ≫ S.arrow))
  rw [← cancel_mono S.arrow, Category.assoc, Subobject.ofLE_arrow, Subobject.push_arrow]
end Subobject
end PretorsionImageClosed
