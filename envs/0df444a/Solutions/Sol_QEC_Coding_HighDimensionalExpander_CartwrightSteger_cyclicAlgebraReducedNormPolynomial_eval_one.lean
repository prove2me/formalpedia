-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraReducedNormPolynomial_eval_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:25:34.1854+00:00
-- url     : https://prove2.me/submissions/c74dcba7-f19f-4d46-916c-3142fbcd4617

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_cyclicAlgebraReducedNormPolynomial
import Theorems.Thm_Matrix_affineLineDet_eval_one


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    Polynomial.eval 1 (cyclicAlgebraReducedNormPolynomial P r x) =
      cyclicAlgebraReducedNormValue P r x := by
  apply (functionFieldEmbedding P r).injective
  calc
    functionFieldEmbedding P r
        (Polynomial.eval 1 (cyclicAlgebraReducedNormPolynomial P r x)) =
      Polynomial.eval (functionFieldEmbedding P r 1)
        (Polynomial.map (functionFieldEmbedding P r)
          (cyclicAlgebraReducedNormPolynomial P r x)) := by
        exact (Polynomial.eval_map_apply
          (p := cyclicAlgebraReducedNormPolynomial P r x)
          (functionFieldEmbedding P r) 1).symm
    _ = Polynomial.eval 1
        (Matrix.affineLineDet
          (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
            (SplittingFunctionField P r))) := by
      rw [map_one, map_cyclicAlgebraReducedNormPolynomial]
    _ = _ := by
      rw [Matrix.affineLineDet_eval_one,
        functionFieldEmbedding_cyclicAlgebraReducedNormValue]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
