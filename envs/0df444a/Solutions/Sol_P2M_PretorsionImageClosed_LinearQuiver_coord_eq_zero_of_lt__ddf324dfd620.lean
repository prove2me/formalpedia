-- Prove2me | solution 1 for P2M_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_lt__ddf324dfd620
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:15:09.834343+00:00
-- url     : https://prove2.me/submissions/722d80c0-7451-4734-984b-dbc00a278af4

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Interval
public import Definitions.Def_PretorsionImageClosed_Subobjects_Preimage
public import Definitions.Def_PretorsionImageClosed_Length_Representations
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Hom
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_not_mem_src
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_not_mem_tgt
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
theorem _root_.solution {c d a b : Fin n} (η : interval k c d ⟶ interval k a b) (hca : c < a)
    (i : Fin n) : coord η i = 0 := by
  by_cases hi : a ≤ i ∧ i ≤ b
  · by_cases hi' : c ≤ i ∧ i ≤ d
    · have := coord_naturality η (hca.le.trans hi.1) ⟨le_rfl, hi'.1.trans hi'.2⟩
      rw [if_pos hi'.2, if_pos hi.2, coord_eq_zero_of_not_mem_tgt η (fun h => hca.not_ge h.1)] at this
      exact this
    · exact coord_eq_zero_of_not_mem_src η hi'
  · exact coord_eq_zero_of_not_mem_tgt η hi
end PretorsionImageClosed.LinearQuiver
