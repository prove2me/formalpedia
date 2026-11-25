-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.mk_eq_suffix_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:42.255641+00:00
-- url     : https://prove2.me/submissions/97666430-886a-45fb-9df8-c7d4b444c03e

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Definitions.Def_PretorsionImageClosed_Subcategories_Trace
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Subobjects
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_eq_scalarHom_comp_canonicalHom
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_scalarHom_zero
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_canonicalHom_le_rfl_eq_intervalIncl
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_not_isZero_interval


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
    (η : interval k c d ⟶ interval k a d) [Mono η] : Subobject.mk η = suffix a d c hac := by
  have hne : coord η c ≠ 0 := by
    intro h0
    have hzero : η = 0 := by
      rw [eq_scalarHom_comp_canonicalHom η hac le_rfl, h0, scalarHom_zero, zero_comp]
    have hm : Mono (0 : interval k c d ⟶ interval k a d) := by
      rw [← hzero]
      infer_instance
    have hz : IsZero (interval k c d) := by
      rw [IsZero.iff_id_eq_zero, ← cancel_mono (0 : interval k c d ⟶ interval k a d), zero_comp,
        comp_zero]
    exact not_isZero_interval hcd hz
  rw [suffix]
  apply Subobject.mk_eq_mk_of_comm _ _ (scalarIso c d hne)
  rw [← canonicalHom_le_rfl_eq_intervalIncl hac]
  exact (eq_scalarHom_comp_canonicalHom η hac le_rfl).symm
end PretorsionImageClosed.LinearQuiver
