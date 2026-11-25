-- Prove2me | solution 1 for PretorsionImageClosed.length_lt_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:39:17.407798+00:00
-- url     : https://prove2.me/submissions/65c3d46c-3c3f-46c0-8002-5801a8910ad3

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
theorem _root_.solution {X Y : C} (f : X ⟶ Y) [Mono f] (h : ¬ IsIso f) : length X < length Y :=
  HasLength.length_lt_of_mono f inferInstance h
end PretorsionImageClosed
