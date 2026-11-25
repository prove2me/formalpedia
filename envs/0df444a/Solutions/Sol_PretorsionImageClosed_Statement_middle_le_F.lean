-- Prove2me | solution 1 for PretorsionImageClosed.Statement.middle_le_F
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:06:40.608797+00:00
-- url     : https://prove2.me/submissions/fd97f80c-d446-45b9-b08b-20b38dea994c

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed
open CategoryTheory Limits ZeroObject
open PretorsionImageClosed.Statement
open Subcategory
variable {C : Type*} [Category C] [Abelian C] [HasLength C]
variable (Z : Subcategory C) (hZ : Z.IsImageClosed)
variable {Z hZ}
variable (hZ : Z.IsImageClosed) (P : PretorsionTheory C) (hP : P.middle = Z.prop)
include hP
namespace PretorsionImageClosed.Statement
theorem _root_.solution : Z.prop ≤ P.F.prop := fun N hN => (hP ▸ hN : P.middle N).2
end PretorsionImageClosed.Statement
