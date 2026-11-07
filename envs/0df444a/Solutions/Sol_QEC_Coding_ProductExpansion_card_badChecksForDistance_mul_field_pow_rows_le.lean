-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_badChecksForDistance_mul_field_pow_rows_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:07:51.406877+00:00
-- url     : https://prove2.me/submissions/33373402-ca61-48a0-bcdb-0a39629b05ac

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_checks_annihilating_nonzero_word_mul_field_pow_rows_eq_total
import Theorems.Thm_QEC_Coding_ProductExpansion_badChecksForDistanceEncoding_injective
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
    Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d) *
        (Nat.card F) ^ Fintype.card R ≤
      Nat.card {c : Word F W // HammingWeight c < d} *
        Nat.card (Matrix R W F) := by
  classical
  let X := {c : Word F W // c ≠ 0 ∧ HammingWeight c < d}
  let E := Σ c : X, {g : Matrix R W F // g.mulVec c.1 = 0}
  have hEncode :
      Nat.card (badChecksForDistance (F := F) (W := W) (R := R) d) ≤
        Nat.card E := Nat.card_le_card_of_injective
      (badChecksForDistanceEncoding (F := F) (W := W) (R := R) d)
      (badChecksForDistanceEncoding_injective
        (F := F) (W := W) (R := R) d)
  have hFiber (c : X) :
      Nat.card {g : Matrix R W F // g.mulVec c.1 = 0} *
          (Nat.card F) ^ Fintype.card R = Nat.card (Matrix R W F) :=
    card_checks_annihilating_nonzero_word_mul_field_pow_rows_eq_total
      (R := R) c.1 c.2.1
  have hSigma : Nat.card E * (Nat.card F) ^ Fintype.card R =
      Nat.card X * Nat.card (Matrix R W F) := by
    rw [Nat.card_sigma, Finset.sum_mul]
    calc
      (∑ c : X, Nat.card {g : Matrix R W F // g.mulVec c.1 = 0} *
          (Nat.card F) ^ Fintype.card R) =
          ∑ _c : X, Nat.card (Matrix R W F) := by
            apply Finset.sum_congr rfl
            intro c hc
            exact hFiber c
      _ = Nat.card X * Nat.card (Matrix R W F) := by
        simp [Nat.card_eq_fintype_card]
  have hX : Nat.card X ≤
      Nat.card {c : Word F W // HammingWeight c < d} :=
    Nat.card_le_card_of_injective
      (fun c : X =>
        (⟨c.1, c.2.2⟩ : {c : Word F W // HammingWeight c < d}))
      (fun c e hce => by
        apply Subtype.ext
        exact congrArg (fun z : {c : Word F W // HammingWeight c < d} => z.1) hce)
  exact (Nat.mul_le_mul_right _ hEncode).trans_eq hSigma |>.trans
    (Nat.mul_le_mul_right _ hX)
end QEC.Coding.ProductExpansion
