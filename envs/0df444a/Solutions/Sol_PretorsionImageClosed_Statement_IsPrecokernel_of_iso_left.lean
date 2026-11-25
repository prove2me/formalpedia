-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsPrecokernel.of_iso_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:23:57.710841+00:00
-- url     : https://prove2.me/submissions/459ba796-11f0-49f8-a1f8-3dc0b944729c

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
namespace IsPrecokernel
theorem _root_.solution {T T' X F : C} {u : T ⟶ X} {v : X ⟶ F}
    (h : IsPrecokernel Z u v) (e : T' ≅ T) : IsPrecokernel Z (e.hom ≫ u) v := by
  refine ⟨by rw [Category.assoc]; exact h.1.comp_left e.hom, fun {Y} v' hv' => ?_⟩
  apply h.2 v'
  have := hv'.comp_left e.inv
  simpa using this
end IsPrecokernel
end PretorsionImageClosed.Statement
