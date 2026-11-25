-- Prove2me | solution 1 for PretorsionImageClosed.imageSubobject_eq_top_of_epi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:39:35.178642+00:00
-- url     : https://prove2.me/submissions/f6f8a5c6-261f-4c83-bdcc-f97d61e21f35

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
theorem _root_.solution {X Y : C} (f : X ⟶ Y) [Epi f] : imageSubobject f = ⊤ := by
  rw [← Subobject.isIso_arrow_iff_eq_top]
  have : Epi (imageSubobject f).arrow := by
    have h := imageSubobject_arrow_comp f
    exact epi_of_epi_fac h
  exact isIso_of_mono_of_epi _
end PretorsionImageClosed
