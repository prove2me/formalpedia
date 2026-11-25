-- Prove2me | solution 1 for PretorsionImageClosed.Statement.le_greatestRealization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:31:13.415775+00:00
-- url     : https://prove2.me/submissions/795a8e42-d125-4603-903b-bd73885cc606

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Theorems.Thm_PretorsionImageClosed_Statement_T_le_upperFirst
public import Theorems.Thm_PretorsionImageClosed_Statement_lowerSecond_le_F

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
theorem _root_.solution : P.LE (greatestRealization Z hZ) :=
  ⟨T_le_upperFirst hZ P hP, lowerSecond_le_F hZ P hP⟩
end PretorsionImageClosed.Statement
