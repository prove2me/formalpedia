-- Prove2me | solution 1 for PretorsionImageClosed.length_eq_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:48:25.229388+00:00
-- url     : https://prove2.me/submissions/9a6f7854-ecc4-49f8-9271-4e0c84b7efe3

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
theorem _root_.solution {X Y : C} (e : X ≅ Y) : length X = length Y :=
  HasLength.length_eq_of_iso e
end PretorsionImageClosed
