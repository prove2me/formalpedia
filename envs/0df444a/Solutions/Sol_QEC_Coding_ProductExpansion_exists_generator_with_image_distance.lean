-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_generator_with_image_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:15:06.411345+00:00
-- url     : https://prove2.me/submissions/04abf629-6996-4fad-acac-5afcb2c837b8

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badGeneratorsForDistance_mul_field_pow_length_le_choose_sum
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
    [DecidableEq W] (d : Nat)
    (hFactor :
      (Nat.card F) ^ Fintype.card R *
        (∑ t : Fin d,
          Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) <
        (Nat.card F) ^ Fintype.card W) :
    ∃ g : Matrix R W F,
      ∀ a : Word F R, a ≠ 0 → d ≤ HammingWeight (g.transpose.mulVec a) := by
  classical
  let Bad := badGeneratorsForDistance (F := F) (W := W) (R := R) d
  let factor := (Nat.card F) ^ Fintype.card R *
    (∑ t : Fin d,
      Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1)
  let penalty := (Nat.card F) ^ Fintype.card W
  let total := Nat.card (Matrix R W F)
  have hBound : Nat.card Bad * penalty ≤ factor * total := by
    simpa [Bad, factor, penalty, total] using
      card_badGeneratorsForDistance_mul_field_pow_length_le_choose_sum
        (F := F) (W := W) (R := R) d
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
      (Subtype.val : badGeneratorsForDistance (F := F) (W := W) (R := R) d →
        Matrix R W F) := by
    intro g
    have hBad : ∃ a : Word F R,
        a ≠ 0 ∧ HammingWeight (g.transpose.mulVec a) < d := by
      exact hNoGood g
    exact ⟨⟨g, hBad⟩, rfl⟩
  have hCardLe := Nat.card_le_card_of_surjective
    (Subtype.val : badGeneratorsForDistance (F := F) (W := W) (R := R) d →
      Matrix R W F) hSurjective
  have hTotalLe : total ≤ Nat.card Bad := by
    change Nat.card (Matrix R W F) ≤
      Nat.card (badGeneratorsForDistance (F := F) (W := W) (R := R) d)
    exact hCardLe
  exact (not_le_of_gt hBadLt) hTotalLe
end QEC.Coding.ProductExpansion
