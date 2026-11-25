-- Prove2me | solution 1 for PretorsionImageClosed.Subobject.exists_maximal_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:23:02.940248+00:00
-- url     : https://prove2.me/submissions/36cd18ae-b126-458f-b9e5-3fed4e51e535

module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Definitions.Def_PretorsionImageClosed_Length_Basic
public import Theorems.Thm_PretorsionImageClosed_length_subobject_le
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
theorem _root_.solution (s : Set (Subobject X)) (hs : s.Nonempty) :
    ∃ S ∈ s, ∀ T ∈ s, S ≤ T → S = T := by
  obtain ⟨S, hS, hmin⟩ :=
    (measure fun S : Subobject X => length X - length (S : C)).wf.has_min s hs
  refine ⟨S, hS, fun T hT hle => Subobject.eq_of_le_of_length_le hle ?_⟩
  have h1 := length_subobject_le S
  have h2 := length_subobject_le T
  have := hmin T hT
  change ¬ (length X - length (T : C) < length X - length (S : C)) at this
  omega
end Subobject
end PretorsionImageClosed
