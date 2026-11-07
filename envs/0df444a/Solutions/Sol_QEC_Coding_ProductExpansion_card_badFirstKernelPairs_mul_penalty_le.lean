-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_badFirstKernelPairs_mul_penalty_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:28:17.038435+00:00
-- url     : https://prove2.me/submissions/554807f3-530f-4c60-acaf-abafa8a97def

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badFirstKernelPairs_le
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badChecksForDistance_mul_field_pow_rows_le_choose_sum
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
variable [Fintype W] [DecidableEq W]
variable [hRFinite : Fintype R] [hR'Finite : Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution (d : Nat) :
    Nat.card (badFirstKernelPairs
        (F := F) (W := W) (R := R) (R' := R') d) *
        (Nat.card F) ^ Fintype.card R ≤
      (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) *
        Nat.card (LocalMatrixPair
          (F := F) (W := W) (R := R) (R' := R')) := by
  calc
    Nat.card (badFirstKernelPairs
        (F := F) (W := W) (R := R) (R' := R') d) *
        (Nat.card F) ^ Fintype.card R ≤
      (Nat.card (badChecksForDistance
          (F := F) (W := W) (R := R) d) * Nat.card (Matrix R' W F)) *
        (Nat.card F) ^ Fintype.card R :=
      Nat.mul_le_mul_right _ (card_badFirstKernelPairs_le
        (F := F) (W := W) (R := R) (R' := R') d)
    _ = (Nat.card (badChecksForDistance
          (F := F) (W := W) (R := R) d) *
        (Nat.card F) ^ Fintype.card R) * Nat.card (Matrix R' W F) := by
      ac_rfl
    _ ≤ ((∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) *
        Nat.card (Matrix R W F)) * Nat.card (Matrix R' W F) :=
      Nat.mul_le_mul_right _
        (card_badChecksForDistance_mul_field_pow_rows_le_choose_sum
          (F := F) (W := W) (R := R) d)
    _ = _ := by
      simp only [LocalMatrixPair, Nat.card_prod]
      simp [mul_assoc]
end QEC.Coding.ProductExpansion
