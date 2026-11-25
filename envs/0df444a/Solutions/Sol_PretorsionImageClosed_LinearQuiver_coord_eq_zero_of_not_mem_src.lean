-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.coord_eq_zero_of_not_mem_src
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:00:42.376269+00:00
-- url     : https://prove2.me/submissions/165fdb93-4f3d-449d-8b35-5e5ae600c10c

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Length_Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_unit_eq_zero_of_not_mem

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable (k : Type u) [Field k] {n : ℕ}
variable {k}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {c d a b : Fin n} (η : interval k c d ⟶ interval k a b)
    {i : Fin n} (h : ¬ (c ≤ i ∧ i ≤ d)) : coord η i = 0 := by
  unfold coord
  rw [unit_eq_zero_of_not_mem k h]
  erw [map_zero]
  rfl
end PretorsionImageClosed.LinearQuiver
