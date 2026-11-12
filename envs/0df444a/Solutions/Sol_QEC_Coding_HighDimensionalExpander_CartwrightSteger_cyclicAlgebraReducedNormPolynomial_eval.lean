-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraReducedNormPolynomial_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:26:03.14686+00:00
-- url     : https://prove2.me/submissions/86bc6ff5-5260-4a47-87a9-7f361eb30c56

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_cyclicAlgebraReducedNormPolynomial
import Theorems.Thm_Matrix_eval_affineLineDet


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) (a : FunctionField P) :
    Polynomial.eval a (cyclicAlgebraReducedNormPolynomial P r x) =
      cyclicAlgebraReducedNormValue P r (1 + a • (x - 1)) := by
  apply (functionFieldEmbedding P r).injective
  calc
    functionFieldEmbedding P r
        (Polynomial.eval a (cyclicAlgebraReducedNormPolynomial P r x)) =
      Polynomial.eval (functionFieldEmbedding P r a)
        (Polynomial.map (functionFieldEmbedding P r)
          (cyclicAlgebraReducedNormPolynomial P r x)) :=
      (Polynomial.eval_map_apply
        (p := cyclicAlgebraReducedNormPolynomial P r x)
        (functionFieldEmbedding P r) a).symm
    _ = Matrix.det ((1 : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) +
        functionFieldEmbedding P r a •
          ((x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) - 1)) := by
      rw [map_cyclicAlgebraReducedNormPolynomial,
        Matrix.eval_affineLineDet]
    _ = Matrix.det
        ((1 + a • (x - 1) : CyclicAlgebra P r) :
          Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r)) := by
      rfl
    _ = _ := by
      rw [← functionFieldEmbedding_cyclicAlgebraReducedNormValue]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
