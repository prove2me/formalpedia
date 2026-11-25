-- Prove2me | solution 1 for PretorsionImageClosed.length_le_of_subobject_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:43:10.851498+00:00
-- url     : https://prove2.me/submissions/d936ca52-f337-4ab2-9340-4708b305d8c1

module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Theorems.Thm_PretorsionImageClosed_length_le_of_mono

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasLength C]
variable {X : C} (S : Subobject X)
namespace PretorsionImageClosed
theorem _root_.solution {S T : Subobject X} (h : S ≤ T) : length (S : C) ≤ length (T : C) :=
  length_le_of_mono (Subobject.ofLE S T h)
end PretorsionImageClosed
