-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsPrecokernel.comp_iso_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:25:47.049802+00:00
-- url     : https://prove2.me/submissions/5fb762ac-9a9d-4088-a3bf-a3a51a04fb8a

module
public import Definitions.Def_PretorsionImageClosed_Subcategories_Basic
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_comp_right


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
namespace IsPrecokernel
theorem _root_.solution {T X F F' : C} {u : T ⟶ X} {v : X ⟶ F}
    (h : IsPrecokernel Z u v) (e : F ≅ F') : IsPrecokernel Z u (v ≫ e.hom) := by
  refine ⟨by rw [← Category.assoc]; exact h.1.comp_right e.hom, fun {Y} v' hv' => ?_⟩
  obtain ⟨w, hw, huniq⟩ := h.2 v' hv'
  refine ⟨e.inv ≫ w, by simp [hw], fun w' hw' => ?_⟩
  rw [← huniq (e.hom ≫ w') (by simpa using hw')]
  simp
end IsPrecokernel
end PretorsionImageClosed.Statement
