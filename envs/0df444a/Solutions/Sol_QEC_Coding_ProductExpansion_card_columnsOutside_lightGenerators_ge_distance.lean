-- Prove2me | solution 1 for QEC.Coding.ProductExpansion.card_columnsOutside_lightGenerators_ge_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:13:43.545018+00:00
-- url     : https://prove2.me/submissions/22046589-106b-4d7c-b1ed-f4db9b76bb51

import Definitions.Def_QEC_Coding_Core_Definitions
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_QEC_Coding_ExpanderCodes_ProductExpansion
import Theorems.Thm_QEC_Coding_ProductExpansion_left_product_rank_pos_of_nonzero_minimal
import Theorems.Thm_QEC_Coding_ProductExpansion_lightGenerators_restrictedWeight_lt_one_sixth
import Theorems.Thm_QEC_Coding_ProductExpansion_card_columnsOutsideSyndromeSpan_ge_distance

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProductExpansion
universe u v
variable {F : Type u} {W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype W] [Fintype R] [Fintype R']
omit [Fintype R]
namespace QEC.Coding.ProductExpansion
theorem _root_.solution
    (h : Matrix R W F) (h' : Matrix R' W F) (d m : Nat)
    (hPositive : 0 < d) (hLength : d ≤ Fintype.card W)
    (hSmallM : 6 * m ≤ d)
    (hDistance : ∀ c : Word F W, c ∈ (parityCheckCode h).carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (hDistance' : ∀ c : Word F W, c ∈ (parityCheckCode h').carrier →
      c ≠ 0 → d ≤ HammingWeight c)
    (x : Matrix W W F) (hx : ProductKernel h h' x)
    (hxNonzero : x ≠ 0)
    (hMinimal : IsDeltaMinimal h h' ((d : ℝ) / 3) x)
    (A : Finset W) (hLargeA : Fintype.card W - m ≤ A.card)
    (C : Finset (Word F W)) (hCard : C.card = (h' * x).rank) :
    d ≤ (columnsOutsideSyndromeSpan h' x (lightGenerators A C d)).card := by
  have hPositiveReal : (0 : ℝ) < d := by exact_mod_cast hPositive
  have hDelta : (d : ℝ) / 3 < d := by linarith
  have hRankPositive := left_product_rank_pos_of_nonzero_minimal
    h h' d hDistance' ((d : ℝ) / 3) hDelta x hxNonzero hMinimal
  have hCPositive : 0 < C.card := by omega
  have hLightWeight := lightGenerators_restrictedWeight_lt_one_sixth
    A C d hCPositive hPositive
  exact card_columnsOutsideSyndromeSpan_ge_distance
    h h' d m hPositive hLength hSmallM hDistance hDistance'
      x hx hxNonzero hMinimal A hLargeA (lightGenerators A C d) hLightWeight
end QEC.Coding.ProductExpansion
