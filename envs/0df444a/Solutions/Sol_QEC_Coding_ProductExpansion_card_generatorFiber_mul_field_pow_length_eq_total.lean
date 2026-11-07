-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_generatorFiber_mul_field_pow_length_eq_total
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:08:21.747459+00:00
-- url     : https://prove2.me/submissions/b245175a-1c48-4cd9-a9dd-17a4f690148b

import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Projection
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansionProbability
import Theorems.Thm_QEC_Coding_ProductExpansion_card_checks_annihilating_nonzero_word_mul_field_pow_rows_eq_total

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (a : Word F R) (ha : a ≠ 0) (y : Word F W) :
    Nat.card {g : Matrix R W F // g.transpose.mulVec a = y} *
        (Nat.card F) ^ Fintype.card W = Nat.card (Matrix R W F) := by
  rw [Nat.card_congr (generatorFiberEquivAnnihilator a ha y)]
  have hCount :=
    card_checks_annihilating_nonzero_word_mul_field_pow_rows_eq_total
      (F := F) (W := R) (R := W) a ha
  calc
    Nat.card {h : Matrix W R F // h.mulVec a = 0} *
        Nat.card F ^ Fintype.card W =
      Nat.card (Matrix W R F) := hCount
    _ = Nat.card (Matrix R W F) :=
      Nat.card_congr (Matrix.transposeLinearEquiv W R F F).toEquiv
end QEC.Coding.ProductExpansion
