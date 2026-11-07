-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.isDeltaMinimal_of_rowLeaders_and_faceColumnMinimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:44:57.262194+00:00
-- url     : https://prove2.me/submissions/e31fd2c3-564e-4db2-ae96-f8e95e3de72b

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_HammingWeight_add_le
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_le_complement_card
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_column_transpose
import Theorems.Thm_QEC_Coding_ProductExpansion_row_transpose
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Coding.ChainComplexData.pureZLogicalQuotientEquivMiddleHomology_mk
attribute [local simp] QEC.Coding.ProductExpansion.HammingWeight_neg
attribute [local simp] QEC.Coding.ProductExpansion.column_transpose
attribute [local simp] QEC.Coding.ProductExpansion.row_transpose
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [DecidableEq W] [Fintype R] [Fintype R']
omit [DecidableEq W] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F)
    (f t : Matrix W W F) (J₃ : Finset W)
    (m : Nat) (beta : ℝ)
    (hJ₃ : Fintype.card W - 2 * m ≤ J₃.card)
    (hAgree : ∀ i ∈ J₃, ∀ j, f i j = t i j)
    (hRowLeaders : ∀ i c,
      c ∈ (parityCheckCode h).carrier →
      HammingWeight (row t i) ≤ HammingWeight (row t i + c))
    (hFaceColumns : ∀ j c,
      c ∈ (parityCheckCode h').carrier →
      (HammingWeight (column f j) : ℝ) ≤
        HammingWeight (column f j + c) + 2)
    (hBudget : 4 * (m : ℝ) + 2 ≤ beta * Fintype.card W) :
    IsDeltaMinimal h h' (beta * Fintype.card W) t := by
  constructor
  · intro i c hc
    have hNonnegative : 0 ≤ beta * Fintype.card W := by
      linarith
    have hLeaderReal : (HammingWeight (row t i) : ℝ) ≤
        HammingWeight (row t i + c) := by
      exact_mod_cast hRowLeaders i c hc
    linarith
  · intro j c hc
    let tf := column t j
    let ff := column f j
    have hVanish : ∀ i ∈ J₃, (ff - tf) i = 0 := by
      intro i hi
      simp [ff, tf, column, hAgree i hi j]
    have hDifferenceNat : HammingWeight (ff - tf) ≤ 2 * m := by
      have hComplement := HammingWeight_le_complement_card J₃ (ff - tf) hVanish
      have hMissing : Fintype.card W - J₃.card ≤ 2 * m := by
        have hJ₃Univ : J₃.card ≤ Fintype.card W := Finset.card_le_univ J₃
        omega
      exact hComplement.trans hMissing
    have hDifferenceReverseNat : HammingWeight (tf - ff) ≤ 2 * m := by
      have hNeg : tf - ff = -(ff - tf) := by abel
      rw [hNeg, HammingWeight_neg]
      exact hDifferenceNat
    have hT : HammingWeight tf ≤
        HammingWeight (tf - ff) + HammingWeight ff := by
      have heq : tf = (tf - ff) + ff := by abel
      calc
        HammingWeight tf = HammingWeight ((tf - ff) + ff) :=
          congrArg HammingWeight heq
        _ ≤ HammingWeight (tf - ff) + HammingWeight ff :=
          HammingWeight_add_le _ _
    have hFCorrected : HammingWeight (ff + c) ≤
        HammingWeight (ff - tf) + HammingWeight (tf + c) := by
      have heq : ff + c = (ff - tf) + (tf + c) := by abel
      calc
        HammingWeight (ff + c) =
            HammingWeight ((ff - tf) + (tf + c)) :=
          congrArg HammingWeight heq
        _ ≤ HammingWeight (ff - tf) + HammingWeight (tf + c) :=
          HammingWeight_add_le _ _
    have hTReal : (HammingWeight tf : ℝ) ≤
        HammingWeight (tf - ff) + HammingWeight ff := by
      exact_mod_cast hT
    have hFCorrectedReal : (HammingWeight (ff + c) : ℝ) ≤
        HammingWeight (ff - tf) + HammingWeight (tf + c) := by
      exact_mod_cast hFCorrected
    have hDifferenceReal : (HammingWeight (ff - tf) : ℝ) ≤ 2 * m := by
      exact_mod_cast hDifferenceNat
    have hDifferenceReverseReal : (HammingWeight (tf - ff) : ℝ) ≤ 2 * m := by
      exact_mod_cast hDifferenceReverseNat
    have hFace := hFaceColumns j c hc
    change (HammingWeight tf : ℝ) ≤
      HammingWeight (tf + c) + beta * Fintype.card W
    linarith
end QEC.Coding.ProductExpansion
