-- Prove2me | solution 1 for PretorsionImageClosed.length_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:36:38.405509+00:00
-- url     : https://prove2.me/submissions/b8f16d61-6d4f-431c-a11d-01d104282872

module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Theorems.Thm_PretorsionImageClosed_length_eq_zero_iff

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasLength C]
namespace PretorsionImageClosed
theorem _root_.solution (X : C) : 0 < length X ↔ ¬ IsZero X := by
  rw [Nat.pos_iff_ne_zero, Ne, length_eq_zero_iff]
end PretorsionImageClosed
