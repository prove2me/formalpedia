-- Prove2me | solution 1 for PretorsionImageClosed.LinearQuiver.indecomposable_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:39.793937+00:00
-- url     : https://prove2.me/submissions/19b34847-1ad8-4431-87ae-f40a6d4fc015

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Decomposition
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_Indecomposables
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_comp
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_zero
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_coord_end_eq
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_hom_ext_coord
public import Theorems.Thm_PretorsionImageClosed_LinearQuiver_not_isZero_interval


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
theorem _root_.solution {a d : Fin n} (had : a ≤ d) : Indecomposable (interval k a d) := by
  refine ⟨not_isZero_interval had, fun Y Z e => ?_⟩
  -- the idempotent cutting out `Y`
  set p : interval k a d ⟶ interval k a d := e.hom ≫ biprod.fst ≫ biprod.inl ≫ e.inv with hp
  have hpp : p ≫ p = p := by
    rw [hp]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.inl_fst_assoc]
  have hl : coord p a * coord p a = coord p a := by
    have := congrArg (fun q => coord q a) hpp
    rwa [coord_comp] at this
  have hl' : coord p a = 0 ∨ coord p a = 1 := by
    rcases eq_or_ne (coord p a) 0 with h | h
    · exact Or.inl h
    · exact Or.inr (mul_left_cancel₀ h (by rw [hl, mul_one]))
  rcases hl' with h0 | h1
  · -- `p = 0`, so `Y` is zero
    have hp0 : p = 0 := hom_ext_coord fun i => by
      rw [coord_end_eq had p i, h0, zero_mul, coord_zero]
    left
    rw [IsZero.iff_id_eq_zero]
    have : (biprod.fst ≫ biprod.inl : Y ⊞ Z ⟶ Y ⊞ Z) = 0 := by
      have h2 : e.inv ≫ p ≫ e.hom = biprod.fst ≫ biprod.inl := by
        rw [hp]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
      rw [← h2, hp0, zero_comp, comp_zero]
    have h3 : (biprod.inl : Y ⟶ Y ⊞ Z) = 0 := by
      have := congrArg (fun q => (biprod.inl : Y ⟶ Y ⊞ Z) ≫ q) this
      simpa using this
    rw [← biprod.inl_fst (X := Y) (Y := Z), h3, zero_comp]
  · -- `p = 𝟙`, so `Z` is zero
    have hp1 : p = 𝟙 _ := hom_ext_coord fun i => by
      rw [coord_end_eq had p i, h1, one_mul]
    right
    rw [IsZero.iff_id_eq_zero]
    have : (biprod.fst ≫ biprod.inl : Y ⊞ Z ⟶ Y ⊞ Z) = 𝟙 _ := by
      have h2 : e.inv ≫ p ≫ e.hom = biprod.fst ≫ biprod.inl := by
        rw [hp]
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
      rw [← h2, hp1, Category.id_comp, Iso.inv_hom_id]
    have := congrArg (fun q => (biprod.inr : Z ⟶ Y ⊞ Z) ≫ q ≫ biprod.snd) this
    simpa using this.symm
end PretorsionImageClosed.LinearQuiver
