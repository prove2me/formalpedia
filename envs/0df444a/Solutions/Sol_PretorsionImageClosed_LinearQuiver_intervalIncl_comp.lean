-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.intervalIncl_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:12:37.007158+00:00
-- url     : https://prove2.me/submissions/36b0383b-0401-4e1c-be09-8895a132791e

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_intervalIncl
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_comp
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_hom_ext_coord


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits Statement
open PretorsionImageClosed.LinearQuiver
universe u
variable {k : Type u} [Field k] {n : ℕ}
namespace PretorsionImageClosed.LinearQuiver
theorem _root_.solution {a ℓ ℓ' d : Fin n} (h : a ≤ ℓ) (h' : ℓ ≤ ℓ') :
    intervalIncl k d h' ≫ intervalIncl k d h = intervalIncl k d (h.trans h') := by
  apply hom_ext_coord
  intro i
  rw [coord_comp, coord_intervalIncl, coord_intervalIncl, coord_intervalIncl]
  by_cases hi : ℓ' ≤ i ∧ i ≤ d
  · rw [if_pos hi, if_pos ⟨h'.trans hi.1, hi.2⟩, one_mul]
  · rw [if_neg hi, zero_mul]
end PretorsionImageClosed.LinearQuiver
