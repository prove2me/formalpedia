-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_complement_rectangle_le_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:00:46.604443+00:00
-- url     : https://prove2.me/submissions/7b911d8e-a95e-4304-b34b-0dba1a54926d

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype F] [DecidableEq F] [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    [DecidableEq W] (A B : Finset W) (m : Nat)
    (hA : Fintype.card W - m ≤ A.card)
    (hB : Fintype.card W - m ≤ B.card) :
    (Finset.univ \ (A ×ˢ B) : Finset (W × W)).card ≤
      2 * m * Fintype.card W := by
  have hAle : A.card ≤ Fintype.card W := Finset.card_le_univ A
  have hBle : B.card ≤ Fintype.card W := Finset.card_le_univ B
  have hwA : Fintype.card W ≤ A.card + m := by omega
  have hwB : Fintype.card W ≤ B.card + m := by omega
  have hMissingA : Fintype.card W - A.card ≤ m := by omega
  have hMissingB : Fintype.card W - B.card ≤ m := by omega
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ (A ×ˢ B)),
    Finset.card_univ, Fintype.card_prod, Finset.card_product]
  calc
    Fintype.card W * Fintype.card W - A.card * B.card =
        (Fintype.card W - A.card) * Fintype.card W +
          A.card * (Fintype.card W - B.card) := by
      rw [Nat.sub_mul, Nat.mul_sub_left_distrib]
      exact (Nat.sub_add_sub_cancel
        (Nat.mul_le_mul_right (Fintype.card W) hAle)
        (Nat.mul_le_mul_left A.card hBle)).symm
    _ ≤ m * Fintype.card W + Fintype.card W * m := by
      exact Nat.add_le_add
        (Nat.mul_le_mul_right (Fintype.card W) hMissingA)
        (Nat.mul_le_mul hAle hMissingB)
    _ = 2 * m * Fintype.card W := by ring
end QEC.Coding.ProductExpansion
