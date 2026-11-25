-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsPrecokernel.epi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:03:37.367469+00:00
-- url     : https://prove2.me/submissions/ecf0757f-0165-4d9f-a983-24418017072f

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
theorem _root_.solution {T X F : C} {u : T ⟶ X} {v : X ⟶ F} (h : IsPrecokernel Z u v) :
    Epi v := by
  refine ⟨fun {Y} a b hab => ?_⟩
  have htriv : IsTrivial Z (u ≫ v ≫ a) := by
    rw [← Category.assoc]
    exact h.1.comp_right a
  obtain ⟨_, -, huniq⟩ := h.2 (v ≫ a) htriv
  exact (huniq a rfl).trans (huniq b hab.symm).symm
end IsPrecokernel
end PretorsionImageClosed.Statement
