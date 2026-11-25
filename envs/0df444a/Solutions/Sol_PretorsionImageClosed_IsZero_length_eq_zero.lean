-- Prove2me | solution 1 for PretorsionImageClosed.IsZero.length_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:39:15.506209+00:00
-- url     : https://prove2.me/submissions/ebd1426d-078f-49d9-bd95-9757d9bbea20

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
namespace IsZero
theorem _root_.solution {X : C} (h : IsZero X) : length X = 0 := (length_eq_zero_iff X).2 h
end IsZero
end PretorsionImageClosed
