-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_productKernel_fixed_word_mul_field_pow_rankLower_le_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:07:39.859442+00:00
-- url     : https://prove2.me/submissions/d5a5ec51-7f9a-4b02-a5d0-a68dba7525f6

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_productKernel_fixed_word_mul_field_pow_rank_eq_total

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [DecidableEq F] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h' : Matrix R' W F) (x : Matrix W W F) (k : Nat)
    (hk : k ≤ (h' * x).rank) :
    Nat.card {h : Matrix R W F // ProductKernel h h' x} *
        (Nat.card F) ^ (k * Fintype.card R) ≤
      Nat.card (Matrix R W F) := by
  have hq : 0 < Nat.card F := Nat.card_pos
  have hExponent : k * Fintype.card R ≤
      (h' * x).rank * Fintype.card R := Nat.mul_le_mul_right _ hk
  have hPow := Nat.pow_le_pow_right hq hExponent
  calc
    Nat.card {h : Matrix R W F // ProductKernel h h' x} *
        (Nat.card F) ^ (k * Fintype.card R) ≤
      Nat.card {h : Matrix R W F // ProductKernel h h' x} *
        (Nat.card F) ^ ((h' * x).rank * Fintype.card R) :=
      Nat.mul_le_mul_left _ hPow
    _ = Nat.card (Matrix R W F) :=
      card_productKernel_fixed_word_mul_field_pow_rank_eq_total h' x
end QEC.Coding.ProductExpansion
