-- Prove2me | solution 1 for PretorsionImageClosed.isZero_of_isIso_biprod_inr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:25:25.042678+00:00
-- url     : https://prove2.me/submissions/e61b3ef2-9a83-4d3e-844a-1bd1b4c4c29d

module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Definitions.Def_PretorsionImageClosed_Biproducts_Basic

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits
namespace PretorsionImageClosed
theorem _root_.solution {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {M N : C} (h : IsIso (biprod.inr : N ⟶ M ⊞ N)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  have h1 : (𝟙 M : M ⟶ M) = biprod.inl ≫ (inv (biprod.inr : N ⟶ M ⊞ N) ≫ biprod.inr) ≫ biprod.fst := by
    rw [IsIso.inv_hom_id, Category.id_comp, biprod.inl_fst]
  rw [h1, Category.assoc, biprod.inr_fst, comp_zero, comp_zero]
end PretorsionImageClosed
