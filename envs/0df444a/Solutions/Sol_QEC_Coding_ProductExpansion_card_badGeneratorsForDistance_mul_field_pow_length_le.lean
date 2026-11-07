-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_badGeneratorsForDistance_mul_field_pow_length_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:10:13.753668+00:00
-- url     : https://prove2.me/submissions/e4fdd43c-74ad-4cd0-9ea6-326ff249944c

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_generatorFiber_mul_field_pow_length_eq_total
import Theorems.Thm_QEC_Coding_ProductExpansion_badGeneratorsForDistanceEncoding_injective
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
      (Nat.card F) ^ Fintype.card R *
        Nat.card {y : Word F W // HammingWeight y < d} *
        Nat.card (Matrix R W F) := by
  classical
  let A := {a : Word F R // a ≠ 0}
  let Y := {y : Word F W // HammingWeight y < d}
  let E := Σ a : A, Σ y : Y,
    {f : Matrix R W F // f.transpose.mulVec a.1 = y.1}
  let penalty := (Nat.card F) ^ Fintype.card W
  let total := Nat.card (Matrix R W F)
  have hEncode :
      Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R) d) ≤
        Nat.card E := Nat.card_le_card_of_injective
      (badGeneratorsForDistanceEncoding (F := F) (W := W) (R := R) d)
      (badGeneratorsForDistanceEncoding_injective
        (F := F) (W := W) (R := R) d)
  have hFiber (a : A) (y : Y) :
      Nat.card {f : Matrix R W F // f.transpose.mulVec a.1 = y.1} *
          penalty = total := by
    simpa [penalty, total] using
      card_generatorFiber_mul_field_pow_length_eq_total
        (W := W) a.1 a.2 y.1
  have hSigma : Nat.card E * penalty = Nat.card A * Nat.card Y * total := by
    rw [Nat.card_sigma, Finset.sum_mul]
    simp_rw [Nat.card_sigma, Finset.sum_mul]
    calc
      (∑ a : A, ∑ y : Y,
          Nat.card {f : Matrix R W F // f.transpose.mulVec a.1 = y.1} *
            penalty) = ∑ _a : A, ∑ _y : Y, total := by
              apply Finset.sum_congr rfl
              intro a ha
              apply Finset.sum_congr rfl
              intro y hy
              exact hFiber a y
      _ = Nat.card A * Nat.card Y * total := by
        simp [Nat.card_eq_fintype_card, mul_assoc]
  have hMessages : Nat.card A ≤ (Nat.card F) ^ Fintype.card R := by
    calc
      Nat.card A ≤ Nat.card (Word F R) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = (Nat.card F) ^ Fintype.card R := by
        rw [Nat.card_fun]
        simp only [Nat.card_eq_fintype_card]
  exact (Nat.mul_le_mul_right penalty hEncode).trans_eq hSigma |>.trans
    (Nat.mul_le_mul_right total (Nat.mul_le_mul_right (Nat.card Y) hMessages))
end QEC.Coding.ProductExpansion
