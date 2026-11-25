-- Prove2me | solution 1 for PretorsionImageClosed.Statement.PretorsionTheory.meet_F
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:41:20.601+00:00
-- url     : https://prove2.me/submissions/bc4fd6c8-dd49-42d4-9daa-c9595277088a

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Partners
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Duality
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Lattice
public import Theorems.Thm_PretorsionImageClosed_Statement_Subcategory_IsImageClosed_iInf


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
theorem _root_.solution (S : Set (PretorsionTheory C)) :
    (meet S).F = Subcategory.iInf (fun F : MeetPartners S => F.1) := rfl
end PretorsionImageClosed.Statement.PretorsionTheory
