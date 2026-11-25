-- Prove2me | solution 1 for PretorsionImageClosed.Statement.isShortPreexact_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:36.549744+00:00
-- url     : https://prove2.me/submissions/e95dfa51-80dc-4797-9a48-db1956e2cc6f

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Basic
public import Definitions.Def_PretorsionImageClosed_Pretorsion_DirectSums
public import Theorems.Thm_PretorsionImageClosed_Statement_IsTrivial_of_prop_src


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits
variable {C : Type*} [Category C] [Abelian C] {Zs : Subcategory C}
namespace PretorsionImageClosed.Statement
theorem _root_.solution {X : C} (hX : Zs.prop X) :
    IsShortPreexact Zs.prop (𝟙 X) (𝟙 X) := by
  refine ⟨⟨IsTrivial.of_prop_src _ hX, ?_⟩, ⟨IsTrivial.of_prop_src _ hX, ?_⟩⟩
  · intro Y u' _
    exact ⟨u', Category.comp_id _, fun w hw => by rw [← hw, Category.comp_id]⟩
  · intro Y v' _
    exact ⟨v', Category.id_comp _, fun w hw => by rw [← hw, Category.id_comp]⟩
end PretorsionImageClosed.Statement
