-- Prove2me | solution 1 for PretorsionImageClosed.imageSubobject_factors_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:38:38.215557+00:00
-- url     : https://prove2.me/submissions/fdef0967-2fdf-46c8-b89f-fb72184141e3

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
theorem _root_.solution {X Y : C} (f : X ⟶ Y) : (imageSubobject f).Factors f :=
  (Subobject.factors_iff _ _).2 ⟨factorThruImageSubobject f, imageSubobject_arrow_comp f⟩
end PretorsionImageClosed
