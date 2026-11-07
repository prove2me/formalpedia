-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.left_product_rank_pos_of_nonzero_minimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:58:27.718378+00:00
-- url     : https://prove2.me/submissions/dd4f5a26-817f-48f2-9773-b5829173364f

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_left_mul_ne_zero_of_nonzero_minimal
import Theorems.Thm_QEC_Coding_ProductExpansion_matrix_rank_pos_of_ne_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (delta : ℝ) (hDelta : delta < d)
    (x : Matrix W W F) (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' delta x) :
    0 < (h' * x).rank :=
  matrix_rank_pos_of_ne_zero (h' * x)
    (left_mul_ne_zero_of_nonzero_minimal h h' d
      hDistance' delta hDelta x hxNonzero hMinimal)
end QEC.Coding.ProductExpansion
