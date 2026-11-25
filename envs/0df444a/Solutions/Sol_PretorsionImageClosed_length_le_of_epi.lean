-- Prove2me | solution 1 for PretorsionImageClosed.length_le_of_epi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:41:38.050233+00:00
-- url     : https://prove2.me/submissions/bff576ae-cf28-47fd-9867-d510ab5dc1e6

module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Theorems.Thm_PretorsionImageClosed_length_eq_of_iso
public import Theorems.Thm_PretorsionImageClosed_length_lt_of_epi

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasLength C]
namespace PretorsionImageClosed
theorem _root_.solution {X Y : C} (f : X ⟶ Y) [Epi f] : length Y ≤ length X := by
  by_cases h : IsIso f
  · exact (length_eq_of_iso (asIso f)).ge
  · exact (length_lt_of_epi f h).le
end PretorsionImageClosed
