-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.coord_end_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:10:01.965962+00:00
-- url     : https://prove2.me/submissions/2f48517b-a680-4a76-97ff-18d1479a1b1f

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_id
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_coord
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_not_mem_src


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {a d : Fin n} (had : a ≤ d) (p : interval k a d ⟶ interval k a d) (i : Fin n) :
    coord p i = coord p a * coord (𝟙 (interval k a d)) i := by
  rw [coord_id]
  by_cases hi : a ≤ i ∧ i ≤ d
  · rw [if_pos hi, mul_one]
    exact coord_eq_coord p le_rfl hi.1 le_rfl hi.2
  · rw [if_neg hi, mul_zero]
    exact coord_eq_zero_of_not_mem_src p hi
end PretorsionImageClosed.LinearQuiver
