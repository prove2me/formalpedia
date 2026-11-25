-- Prove2me | solution 1 for PretorsionImageClosed.Subobject.lt_length_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:43:44.136511+00:00
-- url     : https://prove2.me/submissions/fd7730cc-d95f-46b9-8521-7b22f0a59716

module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Theorems.Thm_PretorsionImageClosed_Subobject_eq_of_le_of_length_le

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
namespace Subobject
theorem _root_.solution {S T : Subobject X} (h : S < T) :
    length (S : C) < length (T : C) := by
  by_contra hl
  exact h.ne (Subobject.eq_of_le_of_length_le h.le (not_lt.1 hl))
end Subobject
end PretorsionImageClosed
