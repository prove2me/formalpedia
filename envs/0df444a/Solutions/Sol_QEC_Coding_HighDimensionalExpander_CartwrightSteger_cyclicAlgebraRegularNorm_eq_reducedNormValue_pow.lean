-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraRegularNorm_eq_reducedNormValue_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:28:47.145947+00:00
-- url     : https://prove2.me/submissions/744567e0-123a-4794-b8b2-55670b36f26b

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_map_cyclicAlgebraRegularNorm_eq_splittingDet_pow

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r) :
    cyclicAlgebraRegularNorm P r x =
      cyclicAlgebraReducedNormValue P r x ^ r.matrixRank := by
  apply (functionFieldEmbedding P r).injective
  rw [map_pow, functionFieldEmbedding_cyclicAlgebraReducedNormValue]
  exact map_cyclicAlgebraRegularNorm_eq_splittingDet_pow P r x
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
