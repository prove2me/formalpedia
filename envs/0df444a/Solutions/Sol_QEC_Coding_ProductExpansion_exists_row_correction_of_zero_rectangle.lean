-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.exists_row_correction_of_zero_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:58:35.94457+00:00
-- url     : https://prove2.me/submissions/bdf1bdc3-d65c-4416-9e18-ee3908faea75

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_exists_code_projection_of_distance
import Theorems.Thm_QEC_Coding_ProductExpansion_leftProduct_sub_mapRows_eq_zero
import Theorems.Thm_QEC_Coding_ProductExpansion_corrected_columns_eq_zero_of_rectangle

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R] [Fintype R']
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F) (d d' : Nat)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d' ≤ HammingWeight c)
    (A B : Finset W) (hLargeA : Fintype.card W - d < A.card)
    (hLargeB : Fintype.card W - d' < B.card)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hRectangle : ∀ i ∈ B, ∀ j ∈ A, x i j = 0) :
    ∃ delta : Matrix W W F,
      h' * (x - delta) = 0 ∧
      (∀ j ∈ A, column (x - delta) j = 0) ∧
      (∀ i : W, row delta i ∈ (parityCheckCode h).carrier) := by
  obtain ⟨T, hFix, hVanish, hImage⟩ :=
    exists_code_projection_of_distance h d hDistance A hLargeA
  refine ⟨mapRows T x, ?_, ?_, ?_⟩
  · exact leftProduct_sub_mapRows_eq_zero h h' x hx T hFix
  · exact corrected_columns_eq_zero_of_rectangle h' d' hDistance'
      A B hLargeB T hVanish x hRectangle
      (leftProduct_sub_mapRows_eq_zero h h' x hx T hFix)
  · intro i
    exact hImage (x i)
end QEC.Coding.ProductExpansion
