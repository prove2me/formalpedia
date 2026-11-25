-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.top_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:42:43.016805+00:00
-- url     : https://prove2.me/submissions/a14cca27-7883-4e9a-9531-e08db3ad5bbc

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_le_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_iff
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_le_top


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
theorem _root_.solution : (⊤ : PretorsionTheory C) = topPT :=
  le_antisymm (le_iff.2
    ⟨fun _ _ => trivial, fun X hX => (⊤ : PretorsionTheory C).F.prop_of_isZero hX⟩) le_top
end PretorsionImageClosed.Statement.PretorsionTheory
