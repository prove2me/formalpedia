-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraReducedNormPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:22:01.513831+00:00
-- url     : https://prove2.me/submissions/77de1aa6-2099-49e2-a4d6-8ebc83ace1ab

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    Polynomial.map (functionFieldEmbedding P r)
        (cyclicAlgebraReducedNormPolynomial P r x) =
      Matrix.affineLineDet
        (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)) :=
  Classical.choose_spec
    (exists_eq_polynomial_map_functionFieldEmbedding_of_frobenius_eq P r
      (Matrix.affineLineDet
        (x : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (SplittingFunctionField P r)))
      (splittingFunctionFieldFrobenius_affineLineDet P r x))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
