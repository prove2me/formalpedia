-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_badChecksAllExactRectangles_mul_rankPenalty_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:14:00.513733+00:00
-- url     : https://prove2.me/submissions/085c9d89-f30a-48fa-8f3c-a0ee9928306e

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badChecksForRectangle_mul_rankPenalty_le_coarse
import Theorems.Thm_QEC_Coding_ProductExpansion_card_exactRectangleSides
import Theorems.Thm_QEC_Coding_ProductExpansion_badChecksAllExactRectanglesEncoding_injective
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
    [DecidableEq W]
    (h' : Matrix R' W F) (s m k : Nat) :
    Nat.card (badChecksAllExactRectangles (R := R) h' s m k) *
        (Nat.card F) ^ (k * Fintype.card R) ≤
      (Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s)) *
        Nat.card (Matrix R W F) := by
  classical
  let penalty := (Nat.card F) ^ (k * Fintype.card R)
  let sparseBound :=
    s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
      (Nat.card F) ^ (2 * m * Fintype.card W + s)
  let total := Nat.card (Matrix R W F)
  have hEncode :
      Nat.card (badChecksAllExactRectangles (R := R) h' s m k) ≤
        Nat.card (Σ A : exactRectangleSides W m,
          Σ B : exactRectangleSides W m,
            badChecksForRectangle (R := R) h' A.1 B.1 s k) :=
    Nat.card_le_card_of_injective
      (badChecksAllExactRectanglesEncoding (R := R) h' s m k)
      (badChecksAllExactRectanglesEncoding_injective (R := R) h' s m k)
  have hEach (A B : exactRectangleSides W m) :
      Nat.card (badChecksForRectangle (R := R) h' A.1 B.1 s k) * penalty ≤
        sparseBound * total := by
    have hA : Fintype.card W - m ≤ A.1.card := by rw [A.2]
    have hB : Fintype.card W - m ≤ B.1.card := by rw [B.2]
    simpa [penalty, sparseBound, total, A.2, B.2] using
      card_badChecksForRectangle_mul_rankPenalty_le_coarse
        (R := R) h' A.1 B.1 s k m hA hB
  have hSigma :
      Nat.card (Σ A : exactRectangleSides W m,
          Σ B : exactRectangleSides W m,
            badChecksForRectangle (R := R) h' A.1 B.1 s k) * penalty ≤
      Nat.card (exactRectangleSides W m) *
        Nat.card (exactRectangleSides W m) * (sparseBound * total) := by
    rw [Nat.card_sigma, Finset.sum_mul]
    simp_rw [Nat.card_sigma, Finset.sum_mul]
    calc
      (∑ A : exactRectangleSides W m, ∑ B : exactRectangleSides W m,
          Nat.card (badChecksForRectangle (R := R) h' A.1 B.1 s k) * penalty) ≤
          ∑ _A : exactRectangleSides W m,
            ∑ _B : exactRectangleSides W m, sparseBound * total := by
            apply Finset.sum_le_sum
            intro A hA
            apply Finset.sum_le_sum
            intro B hB
            exact hEach A B
      _ = Nat.card (exactRectangleSides W m) *
          Nat.card (exactRectangleSides W m) * (sparseBound * total) := by
        simp [Nat.card_eq_fintype_card, mul_assoc]
  have hAll := (Nat.mul_le_mul_right penalty hEncode).trans hSigma
  have hSideCard := card_exactRectangleSides W m
  rw [hSideCard] at hAll
  simpa [penalty, sparseBound, total, pow_two, mul_assoc] using hAll
end QEC.Coding.ProductExpansion
