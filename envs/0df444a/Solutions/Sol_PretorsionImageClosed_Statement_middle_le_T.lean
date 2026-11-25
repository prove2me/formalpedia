-- Prove2me | solution 1 for PretorsionImageClosed.Statement.middle_le_T
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:57:11.37391+00:00
-- url     : https://prove2.me/submissions/a61e2746-d19a-40a3-a6ae-e3d24b3660be

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
theorem _root_.solution : Z.prop ≤ P.T.prop := fun N hN => (hP ▸ hN : P.middle N).1
end PretorsionImageClosed.Statement
