-- Prove2me | solution 1 for PretorsionImageClosed.Subobject.factors_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:19:52.459654+00:00
-- url     : https://prove2.me/submissions/b804a695-dde0-4f47-9e3d-bf7674c298de

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
theorem _root_.solution {X Y : C} (U : Subobject Y) : U.Factors (0 : X ⟶ Y) :=
  (Subobject.factors_iff _ _).2 ⟨0, zero_comp⟩
end Subobject
end PretorsionImageClosed
