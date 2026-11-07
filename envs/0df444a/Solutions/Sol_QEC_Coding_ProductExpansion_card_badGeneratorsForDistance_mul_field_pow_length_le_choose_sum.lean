-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_badGeneratorsForDistance_mul_field_pow_length_le_choose_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:11:58.941615+00:00
-- url     : https://prove2.me/submissions/69158ddf-6316-4aa5-9b57-ebbdcb10036e

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_lowWeightWords_lt_le_choose_sum
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badGeneratorsForDistance_mul_field_pow_length_le
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
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
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    [DecidableEq W] (d : Nat) :
    Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R) d) *
        (Nat.card F) ^ Fintype.card W ≤
      ((Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)) *
        Nat.card (Matrix R W F) := by
  have hBad := card_badGeneratorsForDistance_mul_field_pow_length_le
    (F := F) (W := W) (R := R) d
  have hWords := card_lowWeightWords_lt_le_choose_sum (F := F) (W := W) d
  exact hBad.trans (by
    simpa [mul_assoc, mul_comm, mul_left_comm] using Nat.mul_le_mul_left
      ((Nat.card F) ^ Fintype.card R * Nat.card (Matrix R W F)) hWords)
end QEC.Coding.ProductExpansion
