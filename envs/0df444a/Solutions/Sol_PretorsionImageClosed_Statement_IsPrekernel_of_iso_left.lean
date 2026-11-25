-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsPrekernel.of_iso_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:23:44.981728+00:00
-- url     : https://prove2.me/submissions/0415e772-8113-4f83-8164-1513c2517476

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_comp_left


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits ZeroObject
open PretorsionImageClosed.Statement
variable {C : Type*} [Category C] {Z : ObjectProperty C}
namespace PretorsionImageClosed.Statement
namespace IsPrekernel
theorem _root_.solution {T T' X F : C} {u : T ⟶ X} {v : X ⟶ F} (h : IsPrekernel Z u v)
    (e : T' ≅ T) : IsPrekernel Z (e.hom ≫ u) v := by
  refine ⟨by rw [Category.assoc]; exact h.1.comp_left e.hom, fun {Y} u' hu' => ?_⟩
  obtain ⟨w, hw, huniq⟩ := h.2 u' hu'
  refine ⟨w ≫ e.inv, by simp [hw], fun w' hw' => ?_⟩
  rw [← huniq (w' ≫ e.hom) (by simpa using hw')]
  simp
end IsPrekernel
end PretorsionImageClosed.Statement
