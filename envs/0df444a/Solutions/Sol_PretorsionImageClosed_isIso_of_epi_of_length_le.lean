-- Prove2me | solution 1 for PretorsionImageClosed.isIso_of_epi_of_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:42:20.476455+00:00
-- url     : https://prove2.me/submissions/99b46ede-4e86-4be4-a17c-c0a35e4593e9

module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Definitions.Def_PretorsionImageClosed_Length_Basic
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
theorem _root_.solution {X Y : C} (f : X ⟶ Y) [Epi f] (h : length X ≤ length Y) :
    IsIso f := by
  by_contra hf
  exact absurd (length_lt_of_epi f hf) (not_lt.2 h)
end PretorsionImageClosed
