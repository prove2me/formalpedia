-- Prove2me | solution 1 for PretorsionImageClosed.length_subobject_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:40:55.95072+00:00
-- url     : https://prove2.me/submissions/1579c6dd-73fc-4da2-82c6-45a892a557bc

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
theorem _root_.solution : length (S : C) ≤ length X := length_le_of_mono S.arrow
end PretorsionImageClosed
