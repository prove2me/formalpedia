-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.eq_and_le_of_epi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:52.640834+00:00
-- url     : https://prove2.me/submissions/a1691019-dd6d-4e0d-8bb4-5a4ce9970344

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_le_of_coord_ne_zero
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_epi_iff_surjective
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_app_val
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_not_mem_src
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_unit_val_of_mem


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
theorem _root_.solution {a d a' d' : Fin n} (had' : a' ≤ d') (η : interval k a d ⟶ interval k a' d')
    [Epi η] : a' = a ∧ d' ≤ d := by
  -- `η` is surjective at the vertex `a'`, where the target is nonzero
  have hsurj := (FGModuleCat.epi_iff_surjective (η.app a')).1 ((NatTrans.epi_iff_epi_app η).1 inferInstance a')
  have hne : coord η a' ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := hsurj (unit k a' d' a')
    have := congrArg Subtype.val hx
    rw [app_val, h0, mul_zero, unit_val_of_mem k ⟨le_rfl, had'⟩] at this
    exact zero_ne_one this
  obtain ⟨haa', hdd'⟩ := le_of_coord_ne_zero η hne
  have hmem : a ≤ a' ∧ a' ≤ d := by
    by_contra h
    exact hne (coord_eq_zero_of_not_mem_src η h)
  exact ⟨le_antisymm haa' hmem.1, hdd'⟩
end PretorsionImageClosed.LinearQuiver
