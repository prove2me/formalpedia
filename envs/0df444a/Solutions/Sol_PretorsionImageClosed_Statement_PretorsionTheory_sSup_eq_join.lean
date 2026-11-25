-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.sSup_eq_join
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:42:05.351368+00:00
-- url     : https://prove2.me/submissions/89710a92-2513-4b96-8288-af3b872f21f8

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_isLUB_join

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
theorem _root_.solution (S : Set (PretorsionTheory C)) : sSup S = join S :=
  (isLUB_sSup S).unique (isLUB_join S)
end PretorsionImageClosed.Statement.PretorsionTheory
