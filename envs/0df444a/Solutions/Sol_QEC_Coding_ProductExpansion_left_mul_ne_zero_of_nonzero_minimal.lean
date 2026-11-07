-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.left_mul_ne_zero_of_nonzero_minimal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:55:52.732205+00:00
-- url     : https://prove2.me/submissions/3bd273a7-105d-4ef3-8399-e4bf215f958f

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_eq_zero_of_left_mul_eq_zero_and_minimal

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F) (d : Nat)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (delta : ℝ) (hDelta : delta < d)
    (x : Matrix W W F) (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' delta x) :
    h' * x ≠ 0 := by
  intro hZero
  exact hxNonzero (eq_zero_of_left_mul_eq_zero_and_minimal
    h h' d hDistance' delta hDelta x hZero hMinimal)
end QEC.Coding.ProductExpansion
