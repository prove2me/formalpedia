-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_badForwardRectanglePairs_mul_rankPenalty_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:24:52.492193+00:00
-- url     : https://prove2.me/submissions/c1a7ab07-22b4-4cb8-b348-c0c1abfd0904

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionPairProbability
import Theorems.Thm_QEC_Coding_ChainComplexData_pureZLogicalQuotientEquivMiddleHomology_mk
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_neg
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badChecksAllExactRectangles_mul_rankPenalty_le
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
include hR'Finite
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (s m k : Nat) :
    Nat.card (badForwardRectanglePairs
        (F := F) (W := W) (R := R) (R' := R') s m k) *
        (Nat.card F) ^ (k * Fintype.card R) ≤
      ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) *
        Nat.card (LocalMatrixPair (F := F) (W := W) (R := R) (R' := R')) := by
  classical
  rw [Nat.card_congr (badForwardRectanglePairsEquivSigma
    (F := F) (W := W) (R := R) (R' := R') s m k), Nat.card_sigma,
    Finset.sum_mul]
  calc
    (∑ g' : Matrix R' W F,
        Nat.card (badChecksAllExactRectangles (R := R)
          (generatorImageParityCheck g') s m k) *
          (Nat.card F) ^ (k * Fintype.card R)) ≤
        ∑ _g' : Matrix R' W F,
          (Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
            (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
              (Nat.card F) ^ (2 * m * Fintype.card W + s)) *
            Nat.card (Matrix R W F) := by
      apply Finset.sum_le_sum
      intro g' _hg'
      exact card_badChecksAllExactRectangles_mul_rankPenalty_le
        (R := R) (generatorImageParityCheck g') s m k
    _ = _ := by
      simp [LocalMatrixPair, Nat.card_eq_fintype_card,
        mul_assoc, mul_comm, mul_left_comm]
end QEC.Coding.ProductExpansion
