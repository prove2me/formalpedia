-- Prove2me | solution 1 for PretorsionImageClosed.Subobject.eq_of_le_of_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:21:46.416367+00:00
-- url     : https://prove2.me/submissions/7fabf7e3-b5fa-4b23-b562-1ec2485e2e70

module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Theorems.Thm_PretorsionImageClosed_isIso_of_mono_of_length_le

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
theorem _root_.solution {S T : Subobject X} (h : S ≤ T)
    (hl : length (T : C) ≤ length (S : C)) : S = T := by
  have : IsIso (Subobject.ofLE S T h) := isIso_of_mono_of_length_le _ hl
  refine le_antisymm h (Subobject.le_of_comm (inv (Subobject.ofLE S T h)) ?_)
  rw [IsIso.inv_comp_eq, Subobject.ofLE_arrow]
end Subobject
end PretorsionImageClosed
