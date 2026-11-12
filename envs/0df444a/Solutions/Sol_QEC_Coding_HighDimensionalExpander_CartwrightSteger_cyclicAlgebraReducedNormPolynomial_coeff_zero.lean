-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraReducedNormPolynomial_coeff_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:25:18.91263+00:00
-- url     : https://prove2.me/submissions/9c2e07ff-5bf8-47b1-8c59-9ffe008a5f20

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_cyclicAlgebraReducedNormPolynomial
import Theorems.Thm_Matrix_affineLineDet_coeff_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    (cyclicAlgebraReducedNormPolynomial P r x).coeff 0 = 1 := by
  apply (functionFieldEmbedding P r).injective
  rw [← Polynomial.coeff_map, map_cyclicAlgebraReducedNormPolynomial,
    Matrix.affineLineDet_coeff_zero, map_one]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
