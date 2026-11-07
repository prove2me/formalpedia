-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.productExpanding_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:43:29.950199+00:00
-- url     : https://prove2.me/submissions/b5db91b1-179a-47b1-b50e-629b3888c482

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_isDeltaMinimal_mono

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F)
    {s s' m m' : Nat} {beta beta' : ℝ}
    (hExpand : ProductExpanding h h' s m beta)
    (hs : s' ≤ s) (hm : m' ≤ m) (hbeta : beta' ≤ beta) :
    ProductExpanding h h' s' m' beta' := by
  intro x hx hx0 hMinimal A B hA hB
  have hDelta : beta' * Fintype.card W ≤ beta * Fintype.card W :=
    mul_le_mul_of_nonneg_right hbeta (Nat.cast_nonneg _)
  have hMinimal' := isDeltaMinimal_mono h h' x hDelta hMinimal
  have hA' : Fintype.card W - m ≤ A.card := by omega
  have hB' : Fintype.card W - m ≤ B.card := by omega
  exact hs.trans (hExpand x hx hx0 hMinimal' A B hA' hB')
end QEC.Coding.ProductExpansion
