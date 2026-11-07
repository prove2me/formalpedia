-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.codeword_eq_zero_of_minimality_and_complement_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:59:50.264198+00:00
-- url     : https://prove2.me/submissions/25885438-8459-44ef-a41b-322a47115d6b

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_HammingWeight_le_complement_card
import Theorems.Thm_QEC_Coding_ProductExpansion_codeword_eq_zero_of_minimality_and_small_residual

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (d : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (A : Finset W) (delta : ℝ)
    (hGap : 2 * (Fintype.card W - A.card : ℝ) + delta < d)
    (x c : Word F W) (hc : c ∈ (parityCheckCode h).carrier)
    (hCorrected : ∀ j ∈ A, (x - c) j = 0)
    (hMinimal : (HammingWeight x : ℝ) ≤ HammingWeight (x - c) + delta) :
    c = 0 := by
  have hResidualNat := HammingWeight_le_complement_card A (x - c) hCorrected
  have hResidualReal : (HammingWeight (x - c) : ℝ) ≤
      ((Fintype.card W - A.card : Nat) : ℝ) := by
    exact_mod_cast hResidualNat
  have hAle : A.card ≤ Fintype.card W := Finset.card_le_univ A
  have hComplementCast : ((Fintype.card W - A.card : Nat) : ℝ) =
      (Fintype.card W : ℝ) - A.card := Nat.cast_sub hAle
  have hResidualGap : 2 * (HammingWeight (x - c) : ℝ) + delta < d := by
    linarith
  exact codeword_eq_zero_of_minimality_and_small_residual
    h d hDistance delta x c hc hResidualGap hMinimal
end QEC.Coding.ProductExpansion
