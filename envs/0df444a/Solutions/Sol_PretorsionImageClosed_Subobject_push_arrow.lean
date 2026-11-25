-- Prove2me | solution 1 for PretorsionImageClosed.Subobject.push_arrow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:57:24.336893+00:00
-- url     : https://prove2.me/submissions/977aa79b-d559-4067-831a-0e00154aad2c

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
variable {C : Type*} [Category C] [Abelian C] {X : C} (S : Subobject X) (K : Subobject (S : C))
namespace PretorsionImageClosed
namespace Subobject
theorem _root_.solution :
    (Subobject.push S K).arrow = (Subobject.underlyingIso (K.arrow ≫ S.arrow)).hom ≫ K.arrow ≫ S.arrow :=
  (Subobject.underlyingIso_hom_comp_eq_mk _).symm
end Subobject
end PretorsionImageClosed
