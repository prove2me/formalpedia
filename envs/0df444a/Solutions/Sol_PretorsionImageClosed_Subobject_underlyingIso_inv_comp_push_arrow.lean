-- Prove2me | solution 1 for PretorsionImageClosed.Subobject.underlyingIso_inv_comp_push_arrow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:42:15.889172+00:00
-- url     : https://prove2.me/submissions/bd8d327f-119a-4d8f-98d6-be874c3d82bd

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
    (Subobject.underlyingIso (K.arrow ≫ S.arrow)).inv ≫ (Subobject.push S K).arrow =
      K.arrow ≫ S.arrow :=
  Subobject.underlyingIso_arrow _
end Subobject
end PretorsionImageClosed
