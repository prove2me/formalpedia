-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.join_F
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:48:50.365216+00:00
-- url     : https://prove2.me/submissions/4c370efb-628c-4403-9ebc-7b186ed9c2bb

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
theorem _root_.solution (S : Set (PretorsionTheory C)) : (join S).F = (meetT (PretorsionTheory.op '' S)).unop :=
  rfl
end PretorsionImageClosed.Statement.PretorsionTheory
