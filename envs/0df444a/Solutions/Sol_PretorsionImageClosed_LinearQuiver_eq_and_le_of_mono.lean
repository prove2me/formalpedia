-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.eq_and_le_of_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:50.173802+00:00
-- url     : https://prove2.me/submissions/d8fb5321-caea-4bb6-b6ff-92a58cb3021a

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_le_of_coord_ne_zero
public import Theorems.Thm_PretorsionImageClosed_FGModuleCat_mono_iff_injective
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_app_val
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_eq_zero_of_not_mem_tgt
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
theorem _root_.solution {a' d' a d : Fin n} (had' : a' ≤ d') (η : interval k a' d' ⟶ interval k a d)
    [Mono η] : d' = d ∧ a ≤ a' := by
  -- `η` is injective at the vertex `d'`, where the source is nonzero
  have hinj := (FGModuleCat.mono_iff_injective (η.app d')).1 ((NatTrans.mono_iff_mono_app η).1 inferInstance d')
  have hne : coord η d' ≠ 0 := by
    intro h0
    have h1 : (η.app d').hom.hom (unit k a' d' d') = (η.app d').hom.hom 0 := by
      apply Subtype.ext
      rw [app_val, map_zero]
      change _ = (0 : k)
      rw [h0, mul_zero]
    have := hinj h1
    rw [Subtype.ext_iff, unit_val_of_mem k ⟨had', le_rfl⟩] at this
    exact one_ne_zero this
  obtain ⟨haa', hdd'⟩ := le_of_coord_ne_zero η hne
  have hmem : a ≤ d' ∧ d' ≤ d := by
    by_contra h
    exact hne (coord_eq_zero_of_not_mem_tgt η h)
  exact ⟨le_antisymm hmem.2 hdd', haa'⟩
end PretorsionImageClosed.LinearQuiver
