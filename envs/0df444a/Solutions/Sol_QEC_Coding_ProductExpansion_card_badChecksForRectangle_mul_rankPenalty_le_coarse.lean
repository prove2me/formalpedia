-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_badChecksForRectangle_mul_rankPenalty_le_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:12:14.457287+00:00
-- url     : https://prove2.me/submissions/ae98c29c-1254-468f-bb89-f45e8e21eda6

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_sparseRectangle_lt_le_coarse
import Theorems.Thm_QEC_Coding_ProductExpansion_card_badChecksForRectangle_mul_rankPenalty_le

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
    (h' : Matrix R' W F) (A B : Finset W) (s k m : Nat)
    (hA : Fintype.card W - m ≤ A.card)
    (hB : Fintype.card W - m ≤ B.card) :
    Nat.card (badChecksForRectangle (R := R) h' A B s k) *
        (Nat.card F) ^ (k * Fintype.card R) ≤
      (s * (A.card * B.card + 1) ^ s *
        (Nat.card F) ^ (2 * m * Fintype.card W + s)) *
          Nat.card (Matrix R W F) := by
  have hBad := card_badChecksForRectangle_mul_rankPenalty_le
    (R := R) h' A B s k
  have hSparse := card_sparseRectangle_lt_le_coarse
    (F := F) A B s m hA hB
  exact hBad.trans (Nat.mul_le_mul_right (Nat.card (Matrix R W F)) hSparse)
end QEC.Coding.ProductExpansion
