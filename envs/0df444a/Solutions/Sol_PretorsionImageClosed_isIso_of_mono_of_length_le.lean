-- Prove2me | solution 1 for PretorsionImageClosed.isIso_of_mono_of_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:19:08.576328+00:00
-- url     : https://prove2.me/submissions/14374b96-d878-4df7-b127-fb5c8c529a4b

module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Theorems.Thm_PretorsionImageClosed_length_lt_of_mono

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasLength C]
namespace PretorsionImageClosed
theorem _root_.solution {X Y : C} (f : X ⟶ Y) [Mono f] (h : length Y ≤ length X) :
    IsIso f := by
  by_contra hf
  exact absurd (length_lt_of_mono f hf) (not_lt.2 h)
end PretorsionImageClosed
