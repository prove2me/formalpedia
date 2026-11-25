-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.eq_zero_of_coord_last_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:16:09.605944+00:00
-- url     : https://prove2.me/submissions/ba236751-326a-4bba-bc2b-873df1939e5e

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_scalarHom_comp_canonicalHom
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_scalarHom_zero
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_canonicalHom
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_coord_mul_canonical


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
theorem _root_.solution {a c d : Fin n} (hac : a ≤ c) (hcd : c ≤ d)
    (f : interval k c d ⟶ interval k a d) (h : coord f d = 0) : f = 0 := by
  have hc : coord f c = 0 := by
    have := coord_eq_coord_mul_canonical f hac le_rfl d
    rw [coord_canonicalHom, if_pos ⟨hcd, le_rfl⟩, mul_one] at this
    rw [← this, h]
  rw [eq_scalarHom_comp_canonicalHom f hac le_rfl, hc, scalarHom_zero, zero_comp]
end PretorsionImageClosed.LinearQuiver
