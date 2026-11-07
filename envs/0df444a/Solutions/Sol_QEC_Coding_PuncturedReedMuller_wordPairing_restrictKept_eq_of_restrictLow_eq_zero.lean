-- Prove2me | solution 1 for QEC.Coding.PuncturedReedMuller.wordPairing_restrictKept_eq_of_restrictLow_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:03:49.899746+00:00
-- url     : https://prove2.me/submissions/92040495-c83d-4f44-9038-b6e3248a4ecc

import Definitions.Def_QEC_Coding_ReedMuller_Base
import Definitions.Def_QEC_Coding_ReedMuller_Punctured
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PuncturedReedMuller
open ReedMuller
namespace QEC.Coding.PuncturedReedMuller
theorem _root_.solution
    {m w : Nat} (left right : Word (ZMod 2) (BooleanPoint m))
    (hlow : restrictLow m w left = 0) :
    wordPairing (restrictKept m w left) (restrictKept m w right) =
      wordPairing left right := by
  classical
  have hlowPoint (point : LowPoint m w) : left point.1 = 0 := by
    have happly := congrFun hlow point
    simpa using happly
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (fun point : BooleanPoint m => pointWeight point ≤ w)
      (fun point => left point * right point)
  let complementKept :
      {point : BooleanPoint m // ¬ pointWeight point ≤ w} ≃ KeptPoint m w :=
    { toFun := fun point => ⟨point.1, by omega⟩
      invFun := fun point => ⟨point.1, by omega⟩
      left_inv := fun point => Subtype.ext rfl
      right_inv := fun point => Subtype.ext rfl }
  change
    (∑ point : KeptPoint m w, left point.1 * right point.1) =
      ∑ point : BooleanPoint m, left point * right point
  have hlowSum :
      (∑ point : LowPoint m w, left point.1 * right point.1) = 0 := by
    apply Finset.sum_eq_zero
    intro point _hpoint
    rw [hlowPoint]
    simp
  have hcomplement :
      (∑ point : {point : BooleanPoint m // ¬ pointWeight point ≤ w},
        left point.1 * right point.1) =
        ∑ point : BooleanPoint m, left point * right point := by
    simpa only [LowPoint, hlowSum, zero_add] using hsplit
  have hequiv :
      (∑ point : {point : BooleanPoint m // ¬ pointWeight point ≤ w},
        left point.1 * right point.1) =
        ∑ point : KeptPoint m w, left point.1 * right point.1 := by
    exact Fintype.sum_equiv complementKept _ _ (fun _ => rfl)
  exact hequiv.symm.trans hcomplement
end QEC.Coding.PuncturedReedMuller
