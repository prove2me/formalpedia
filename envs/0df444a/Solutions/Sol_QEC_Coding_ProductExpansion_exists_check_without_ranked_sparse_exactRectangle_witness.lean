-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_check_without_ranked_sparse_exactRectangle_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:43:57.126429+00:00
-- url     : https://prove2.me/submissions/1aa0d94b-016d-49e2-a00a-e41f9d4beef0

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badChecksAllExactRectangles_mul_rankPenalty_le
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
    (h' : Matrix R' W F) (s m k : Nat)
    (hFactor :
      (Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
        (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
          (Nat.card F) ^ (2 * m * Fintype.card W + s)) <
        (Nat.card F) ^ (k * Fintype.card R)) :
    ∃ h : Matrix R W F,
      ¬∃ A B : Finset W,
        A.card = Fintype.card W - m ∧
        B.card = Fintype.card W - m ∧
        ∃ x : Matrix W W F,
          restrictedWeight x A B < s ∧
          k ≤ (h' * x).rank ∧ ProductKernel h h' x := by
  classical
  let Bad := badChecksAllExactRectangles (R := R) h' s m k
  let factor :=
    (Nat.choose (Fintype.card W) (Fintype.card W - m)) ^ 2 *
      (s * (((Fintype.card W - m) * (Fintype.card W - m) + 1) ^ s) *
        (Nat.card F) ^ (2 * m * Fintype.card W + s))
  let penalty := (Nat.card F) ^ (k * Fintype.card R)
  let total := Nat.card (Matrix R W F)
  have hBound : Nat.card Bad * penalty ≤ factor * total := by
    simpa [Bad, factor, penalty, total] using
      card_badChecksAllExactRectangles_mul_rankPenalty_le
        (R := R) h' s m k
  have hTotalPositive : 0 < total := Nat.card_pos
  have hBadLt : Nat.card Bad < total := by
    by_contra hNot
    have hTotalLe : total ≤ Nat.card Bad := le_of_not_gt hNot
    have hContradiction : total * penalty < penalty * total :=
      (Nat.mul_le_mul_right penalty hTotalLe).trans_lt <|
        hBound.trans_lt <| by
          simpa [factor, penalty, total] using
            Nat.mul_lt_mul_of_pos_right hFactor hTotalPositive
    simp [mul_comm] at hContradiction
  by_contra hNoGood
  push Not at hNoGood
  have hSurjective : Function.Surjective
      (Subtype.val : badChecksAllExactRectangles (R := R) h' s m k →
        Matrix R W F) := by
    intro h
    exact ⟨⟨h, hNoGood h⟩, rfl⟩
  have hCardLe : Fintype.card (Matrix R W F) ≤
      Fintype.card (badChecksAllExactRectangles (R := R) h' s m k) :=
    Fintype.card_le_of_surjective
      (Subtype.val : badChecksAllExactRectangles (R := R) h' s m k →
        Matrix R W F) hSurjective
  have hTotalLeBad : total ≤ Nat.card Bad := by
    change Nat.card (Matrix R W F) ≤
      Nat.card (badChecksAllExactRectangles (R := R) h' s m k)
    simpa only [Nat.card_eq_fintype_card] using hCardLe
  exact (not_le_of_gt hBadLt) hTotalLeBad
end QEC.Coding.ProductExpansion
