-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_badChecksForDistance_mul_field_pow_rows_le_choose_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:09:37.902759+00:00
-- url     : https://prove2.me/submissions/da60732d-cc7a-4f5c-b4ac-0ab58bf6c90a

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_lowWeightWords_lt_le_choose_sum
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badChecksForDistance_mul_field_pow_rows_le

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
      (∑ t : Fin d,
        Nat.choose (Fintype.card W) t.1 * (Nat.card F) ^ t.1) *
        Nat.card (Matrix R W F) := by
  exact (card_badChecksForDistance_mul_field_pow_rows_le
    (F := F) (W := W) (R := R) d).trans
      (Nat.mul_le_mul_right _
        (card_lowWeightWords_lt_le_choose_sum (F := F) (W := W) d))
end QEC.Coding.ProductExpansion
