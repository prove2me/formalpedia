-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.bot_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:42:32.378241+00:00
-- url     : https://prove2.me/submissions/7261aa9c-84d5-45cf-bf9a-54e6d319234f

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_le_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_bot_le
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_iff


set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open CategoryTheory Limits Subcategory
variable {C : Type*} [Category C] [Abelian C]
variable [HasLength C]
open PretorsionImageClosed.Statement.PretorsionTheory
namespace PretorsionImageClosed.Statement.PretorsionTheory
theorem _root_.solution : (⊥ : PretorsionTheory C) = botPT :=
  le_antisymm bot_le (le_iff.2
    ⟨fun X hX => (⊥ : PretorsionTheory C).T.prop_of_isZero hX, fun _ _ => trivial⟩)
end PretorsionImageClosed.Statement.PretorsionTheory
