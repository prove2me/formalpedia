-- Prove2me | solution 1 for PretorsionImageClosed.Subobject.exists_minimal_of_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:23:37.875809+00:00
-- url     : https://prove2.me/submissions/5aa7be91-e6a7-4ac2-8678-0d14292bc792

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
theorem _root_.solution (s : Set (Subobject X)) (hs : s.Nonempty) :
    ∃ S ∈ s, ∀ T ∈ s, T ≤ S → T = S := by
  obtain ⟨S, hS, hmin⟩ :=
    (measure fun S : Subobject X => length (S : C)).wf.has_min s hs
  refine ⟨S, hS, fun T hT hle => Subobject.eq_of_le_of_length_le hle ?_⟩
  have := hmin T hT
  change ¬ (length (T : C) < length (S : C)) at this
  exact not_lt.1 this
end Subobject
end PretorsionImageClosed
