-- Prove2me | solution 1 for PretorsionImageClosed.length_le_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:37:16.694481+00:00
-- url     : https://prove2.me/submissions/971df98e-2830-40a0-9f81-70d943eedce8

module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Theorems.Thm_PretorsionImageClosed_length_eq_of_iso
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
theorem _root_.solution {X Y : C} (f : X ⟶ Y) [Mono f] : length X ≤ length Y := by
  by_cases h : IsIso f
  · exact (length_eq_of_iso (asIso f)).le
  · exact (length_lt_of_mono f h).le
end PretorsionImageClosed
