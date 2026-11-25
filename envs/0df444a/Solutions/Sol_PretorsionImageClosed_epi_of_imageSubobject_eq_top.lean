-- Prove2me | solution 1 for PretorsionImageClosed.epi_of_imageSubobject_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:40:03.826986+00:00
-- url     : https://prove2.me/submissions/8cad299a-c8a7-494b-ac35-cd273ab914f2

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
theorem _root_.solution {X Y : C} (f : X ⟶ Y) (h : imageSubobject f = ⊤) : Epi f := by
  have : IsIso (imageSubobject f).arrow := (Subobject.isIso_arrow_iff_eq_top _).2 h
  rw [← imageSubobject_arrow_comp f]
  exact epi_comp _ _
end PretorsionImageClosed
