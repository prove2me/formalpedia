-- Prove2me | solution 1 for PretorsionImageClosed.length_lt_of_epi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:39:35.325849+00:00
-- url     : https://prove2.me/submissions/91661b4a-8f51-47a7-925c-e42d23bbb67c

module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Definitions.Def_PretorsionImageClosed_Length_Basic

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasLength C]
namespace PretorsionImageClosed
theorem _root_.solution {X Y : C} (f : X ⟶ Y) [Epi f] (h : ¬ IsIso f) : length Y < length X :=
  HasLength.length_lt_of_epi f inferInstance h
end PretorsionImageClosed
