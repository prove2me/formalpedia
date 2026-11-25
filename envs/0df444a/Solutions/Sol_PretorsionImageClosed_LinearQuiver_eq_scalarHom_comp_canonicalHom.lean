-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.eq_scalarHom_comp_canonicalHom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:10:50.910983+00:00
-- url     : https://prove2.me/submissions/ee48f683-9f00-4b82-aa3f-4ea0974803fb

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_canonicalHom
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_comp
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_coord_mul_canonical
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_id
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
theorem _root_.solution {c d a b : Fin n} (η : interval k c d ⟶ interval k a b)
    (hac : a ≤ c) (hbd : b ≤ d) :
    η = scalarHom c d (coord η c) ≫ canonicalHom hac hbd := by
  apply hom_ext_coord
  intro i
  rw [coord_comp, coord_scalarHom, coord_eq_coord_mul_canonical η hac hbd i, coord_canonicalHom,
    coord_id]
  by_cases hi : c ≤ i ∧ i ≤ b
  · rw [if_pos hi, if_pos ⟨hi.1, hi.2.trans hbd⟩]
    ring
  · rw [if_neg hi, mul_zero, mul_zero]
end PretorsionImageClosed.LinearQuiver
