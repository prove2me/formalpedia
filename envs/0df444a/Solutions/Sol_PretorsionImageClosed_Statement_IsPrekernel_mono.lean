-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsPrekernel.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:48:37.6043+00:00
-- url     : https://prove2.me/submissions/532271be-36ca-4967-9e5e-322f67dc028d

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
theorem _root_.solution {T X F : C} {u : T ⟶ X} {v : X ⟶ F} (h : IsPrekernel Z u v) : Mono u := by
  refine ⟨fun {Y} a b hab => ?_⟩
  have htriv : IsTrivial Z ((a ≫ u) ≫ v) := by
    rw [Category.assoc]
    exact h.1.comp_left a
  obtain ⟨_, -, huniq⟩ := h.2 (a ≫ u) htriv
  exact (huniq a rfl).trans (huniq b hab.symm).symm
end IsPrekernel
end PretorsionImageClosed.Statement
