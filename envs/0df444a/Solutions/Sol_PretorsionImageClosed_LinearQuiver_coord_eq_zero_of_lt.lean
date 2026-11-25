-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.coord_eq_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:14:57.423362+00:00
-- url     : https://prove2.me/submissions/5f111fb7-6c3e-47d5-ab0c-c9722de71b4b

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Length_Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_not_mem_src
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_naturality

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
theorem _root_.solution {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) (hdb : d < b)
    (i : Fin n) : coord η i = 0 := by
  by_cases hi : c ≤ i ∧ i ≤ d
  · have := coord_naturality η (hi.2.trans hdb.le) hi
    rw [if_neg (not_le.2 hdb), if_pos le_rfl] at this
    exact this.symm
  · exact coord_eq_zero_of_not_mem_src η hi
end PretorsionImageClosed.LinearQuiver
