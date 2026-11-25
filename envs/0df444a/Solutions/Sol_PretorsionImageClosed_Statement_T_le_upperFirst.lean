-- Prove2me | solution 1 for PretorsionImageClosed.Statement.T_le_upperFirst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:07:49.05522+00:00
-- url     : https://prove2.me/submissions/1dbf3c01-dd29-41b0-87f6-90999d21268c

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Theorems.Thm_PretorsionImageClosed_Statement_middle_le_F
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isQuotientClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isSubobjectClosed


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
theorem _root_.solution : P.T.prop ≤ (upperFirst Z hZ).prop := by
  intro X hX N f hN
  have hT : P.T.IsQuotientClosed := P.isPretorsionTheory.isQuotientClosed
  have hF : P.F.IsSubobjectClosed := P.isPretorsionTheory.isSubobjectClosed
  have : P.middle (imageSubobject f : C) :=
    ⟨hT (factorThruImageSubobject f) inferInstance hX,
      hF (imageSubobject f).arrow inferInstance (middle_le_F P hP N hN)⟩
  rwa [hP] at this
end PretorsionImageClosed.Statement
