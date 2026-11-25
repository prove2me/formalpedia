-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsPrekernel.comp_iso_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:23:53.886521+00:00
-- url     : https://prove2.me/submissions/87f7ca6c-5af9-4bfc-afc7-0f49bf6db30f

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
namespace IsPrekernel
theorem _root_.solution {T X F F' : C} {u : T ⟶ X} {v : X ⟶ F} (h : IsPrekernel Z u v)
    (e : F ≅ F') : IsPrekernel Z u (v ≫ e.hom) := by
  refine ⟨by rw [← Category.assoc]; exact h.1.comp_right e.hom, fun {Y} u' hu' => ?_⟩
  apply h.2 u'
  have := hu'.comp_right e.inv
  simpa using this
end IsPrekernel
end PretorsionImageClosed.Statement
