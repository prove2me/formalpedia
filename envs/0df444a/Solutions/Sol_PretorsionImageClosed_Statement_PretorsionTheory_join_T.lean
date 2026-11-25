-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.join_T
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:48:47.213986+00:00
-- url     : https://prove2.me/submissions/6b0ef749-9cd0-45c4-800c-1766428fbe30

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice

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
theorem _root_.solution (S : Set (PretorsionTheory C)) : (join S).T = (meet (PretorsionTheory.op '' S)).F.unop :=
  rfl
end PretorsionImageClosed.Statement.PretorsionTheory
