-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_check_with_distance_without_ranked_sparse_exactRectangle_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:17:06.160701+00:00
-- url     : https://prove2.me/submissions/100d417b-4b62-41c2-8c09-8693b1fea5b8

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badChecksForDistance_mul_field_pow_rows_le_choose_sum
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badChecksAllExactRectangles_mul_rankPenalty_le
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badChecksDistanceOrRectangles_le_add
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
set_option maxHeartbeats 800000
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    [DecidableEq W]
    (h' : Matrix R' W F) (d s m k : Nat)
    (hDistanceFactor :
      2 * (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card R)
    (hRectangleFactor :
      2 * ((Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s))) <
        (Nat.card F) ^ (k * Fintype.card R)) :
    ∃ h : Matrix R W F,
      (∀ c : Word F W, h.mulVec c = 0 → c ≠ 0 → d ≤ HammingWeight c) ∧
      ¬∃ A B : Finset W,
        A.card = Fintype.card W - m ∧
        B.card = Fintype.card W - m ∧
        ∃ x : Matrix W W F,
          restrictedWeight x A B < s ∧
          k ≤ (h' * x).rank ∧ ProductKernel h h' x := by
  classical
  let distanceFactor := ∑ t : Fin d,
    Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1
  let distancePenalty := (Nat.card F) ^ Fintype.card R
  let rectangleFactor :=
    (Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
      (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
        (Nat.card F) ^ (2 * m * Fintype.card W + s))
  let rectanglePenalty := (Nat.card F) ^ (k * Fintype.card R)
  let distanceBad :=
    Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d)
  let rectangleBad :=
    Nat.card (badChecksAllExactRectangles (R := R) h' s m k)
  let total := Nat.card (Matrix R W F)
  have hTotalPositive : 0 < total := Nat.card_pos
  have hDistanceBound : distanceBad * distancePenalty ≤ distanceFactor * total := by
    simpa [distanceBad, distancePenalty, distanceFactor, total] using
      card_badChecksForDistance_mul_field_pow_rows_le_choose_sum
        (F := F) (W := W) (R := R) d
  have hRectangleBound : rectangleBad * rectanglePenalty ≤
      rectangleFactor * total := by
    simpa [rectangleBad, rectanglePenalty, rectangleFactor, total] using
      card_badChecksAllExactRectangles_mul_rankPenalty_le
        (R := R) h' s m k
  have hDistanceHalf : 2 * distanceBad < total := by
    have hScaled : (2 * distanceBad) * distancePenalty < total * distancePenalty := by
      calc
        (2 * distanceBad) * distancePenalty =
            2 * (distanceBad * distancePenalty) := by simp [mul_assoc]
        _ ≤ 2 * (distanceFactor * total) := Nat.mul_le_mul_left 2 hDistanceBound
        _ = (2 * distanceFactor) * total := by simp [mul_assoc]
        _ < distancePenalty * total :=
          Nat.mul_lt_mul_of_pos_right (by simpa [distanceFactor, distancePenalty] using
            hDistanceFactor) hTotalPositive
        _ = total * distancePenalty := Nat.mul_comm _ _
    exact Nat.lt_of_mul_lt_mul_right hScaled
  have hRectangleHalf : 2 * rectangleBad < total := by
    have hScaled : (2 * rectangleBad) * rectanglePenalty < total * rectanglePenalty := by
      calc
        (2 * rectangleBad) * rectanglePenalty =
            2 * (rectangleBad * rectanglePenalty) := by simp [mul_assoc]
        _ ≤ 2 * (rectangleFactor * total) := Nat.mul_le_mul_left 2 hRectangleBound
        _ = (2 * rectangleFactor) * total := by simp [mul_assoc]
        _ < rectanglePenalty * total :=
          Nat.mul_lt_mul_of_pos_right
            (by simpa [rectangleFactor, rectanglePenalty] using hRectangleFactor)
            hTotalPositive
        _ = total * rectanglePenalty := Nat.mul_comm _ _
    exact Nat.lt_of_mul_lt_mul_right hScaled
  have hBadLt :
      Nat.card (badChecksDistanceOrRectangles (R := R) h' d s m k) < total :=
    (card_badChecksDistanceOrRectangles_le_add
      (R := R) h' d s m k).trans_lt (by omega)
  have hExists : ∃ h : Matrix R W F,
      ¬((∃ c : Word F W,
          c ≠ 0 ∧ HammingWeight c < d ∧ h.mulVec c = 0) ∨
        (∃ A B : Finset W,
          A.card = Fintype.card W - m ∧
          B.card = Fintype.card W - m ∧
          ∃ x : Matrix W W F,
            restrictedWeight x A B < s ∧
            k ≤ (h' * x).rank ∧ ProductKernel h h' x)) := by
    by_contra hNo
    have hSurjective : Function.Surjective
        (Subtype.val : badChecksDistanceOrRectangles (R := R) h' d s m k →
          Matrix R W F) := by
      intro h
      have hBad :
          (∃ c : Word F W,
            c ≠ 0 ∧ HammingWeight c < d ∧ h.mulVec c = 0) ∨
          (∃ A B : Finset W,
            A.card = Fintype.card W - m ∧
            B.card = Fintype.card W - m ∧
            ∃ x : Matrix W W F,
              restrictedWeight x A B < s ∧
              k ≤ (h' * x).rank ∧ ProductKernel h h' x) := by
        by_contra hGood
        exact hNo ⟨h, hGood⟩
      exact ⟨⟨h, hBad⟩, rfl⟩
    have hCardLe := Nat.card_le_card_of_surjective
      (Subtype.val : badChecksDistanceOrRectangles (R := R) h' d s m k →
        Matrix R W F) hSurjective
    have hTotalLe : total ≤
        Nat.card (badChecksDistanceOrRectangles (R := R) h' d s m k) := by
      dsimp only [total]
      exact hCardLe
    exact (not_le_of_gt hBadLt) hTotalLe
  obtain ⟨h, hGood⟩ := hExists
  have hDistanceGood := (not_or.mp hGood).1
  have hRectangleGood := (not_or.mp hGood).2
  refine ⟨h, ?_, hRectangleGood⟩
  intro c hcKernel hcNonzero
  exact Nat.le_of_not_gt (fun hcWeight =>
    hDistanceGood ⟨c, hcNonzero, hcWeight, hcKernel⟩)
end QEC.Coding.ProductExpansion
