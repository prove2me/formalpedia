-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_sparseRectangle_lt_le_coarse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:04:57.2982+00:00
-- url     : https://prove2.me/submissions/789b9c93-1e44-4e18-8e5f-71d6b510c02a

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_sparseRectangle_lt_le_choose_sum
import Theorems.Thm_QEC_Coding_ProductExpansion_choose_power_sum_le
import Theorems.Thm_QEC_Coding_ProductExpansion_card_complement_rectangle_le_two_mul

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    [DecidableEq W] (A B : Finset W) (s m : Nat)
    (hA : Fintype.card W - m ≤ A.card)
    (hB : Fintype.card W - m ≤ B.card) :
    Nat.card {x : Matrix W W F // restrictedWeight x A B < s} ≤
      s * (A.card * B.card + 1) ^ s *
        (Nat.card F) ^ (2 * m * Fintype.card W + s) := by
  have hCount := card_sparseRectangle_lt_le_choose_sum (F := F) A B s
  have hSum := choose_power_sum_le (A.card * B.card)
    (Finset.univ \ (A ×ˢ B) : Finset (W × W)).card s (Nat.card F)
    (Nat.card_pos)
  have hOutside := card_complement_rectangle_le_two_mul A B m hA hB
  have hExponent :
      (Finset.univ \ (A ×ˢ B) : Finset (W × W)).card + s ≤
        2 * m * Fintype.card W + s := Nat.add_le_add_right hOutside s
  have hPow := Nat.pow_le_pow_right (Nat.card_pos (α := F)) hExponent
  exact hCount.trans <| hSum.trans <|
    Nat.mul_le_mul_left (s * (A.card * B.card + 1) ^ s) hPow
end QEC.Coding.ProductExpansion
