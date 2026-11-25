-- Prove2me | solution 1 for PretorsionImageClosed.Statement.lowerSecond_le_F
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:27:31.078747+00:00
-- url     : https://prove2.me/submissions/c5341dff-6e36-4200-b244-c149472da76c

module
public import Definitions.Def_PretorsionImageClosed_Pretorsion_Realization
public import Definitions.Def_PretorsionImageClosed_Realizations_TheoremA
public import Theorems.Thm_PretorsionImageClosed_Statement_middle_le_F
public import Theorems.Thm_PretorsionImageClosed_Statement_T_le_upperFirst
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_isSubobjectClosed
public import Theorems.Thm_PretorsionImageClosed_Statement_IsPretorsionTheory_prop_iff_prop_trace


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
theorem _root_.solution : (lowerSecond Z hZ).prop ≤ P.F.prop := by
  intro Y hY
  have hF : P.F.IsSubobjectClosed := P.isPretorsionTheory.isSubobjectClosed
  rw [P.isPretorsionTheory.prop_iff_prop_trace]
  have hle : P.T.trace Y ≤ (upperFirst Z hZ).trace Y :=
    le_trace (upperFirst_isQuotientClosed Z hZ) (T_le_upperFirst hZ P hP _ (P.T.prop_trace Y))
  exact ⟨P.T.prop_trace Y,
    hF (Subobject.ofLE _ _ hle) inferInstance (middle_le_F P hP _ hY)⟩
end PretorsionImageClosed.Statement
