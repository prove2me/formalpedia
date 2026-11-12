-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraReducedNormPolynomial_eq_buildingAffineLineDet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:36:38.558122+00:00
-- url     : https://prove2.me/submissions/abd34dbb-7245-4f65-889d-def4a0b535a6

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cyclicAlgebraReducedNormPolynomial_coeff_zero
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_cyclicAlgebraReducedNormPolynomial_pow_eq_buildingAffineLineDet_pow
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_matrixRank_isUnit_buildingLocalField
import Theorems.Thm_Matrix_affineLineDet_coeff_zero
import Theorems.Thm_Polynomial_eq_of_pow_eq_pow_of_coeff_zero_eq_one


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    Polynomial.map (algebraMap (FunctionField P) (BuildingLocalField P))
        (cyclicAlgebraReducedNormPolynomial P r x) =
      Matrix.affineLineDet (cyclicAlgebraToBuilding P r x) := by
  apply Polynomial.eq_of_pow_eq_pow_of_coeff_zero_eq_one
    (matrixRank_isUnit_buildingLocalField P r)
  · rw [Polynomial.coeff_map,
      cyclicAlgebraReducedNormPolynomial_coeff_zero, map_one]
  · exact Matrix.affineLineDet_coeff_zero _
  · exact
      map_cyclicAlgebraReducedNormPolynomial_pow_eq_buildingAffineLineDet_pow
        P r x
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
