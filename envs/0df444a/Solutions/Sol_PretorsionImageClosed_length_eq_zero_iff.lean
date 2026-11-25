-- Prove2me | solution 1 for PretorsionImageClosed.length_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:30:48.99905+00:00
-- url     : https://prove2.me/submissions/5b441709-b954-45ad-8d86-9ca7a8f5e785

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
theorem _root_.solution (X : C) : length X = 0 ↔ IsZero X := HasLength.length_eq_zero_iff X
end PretorsionImageClosed
