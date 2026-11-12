-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraReducedNorm_baseChange_eq_splitReducedNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T16:24:46.539308+00:00
-- url     : https://prove2.me/submissions/d735f659-ad69-4768-a37a-24aab022ca1b

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
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    Units.map (functionFieldEmbedding P r)
        (cyclicAlgebraReducedNorm P r u) =
      cyclicAlgebraSplitReducedNorm P r u := by
  apply Units.ext
  change functionFieldEmbedding P r
      (cyclicAlgebraReducedNormValue P r (u : CyclicAlgebra P r)) =
    Matrix.det (u : Matrix (Fin r.matrixRank) (Fin r.matrixRank)
      (SplittingFunctionField P r))
  exact functionFieldEmbedding_cyclicAlgebraReducedNormValue P r u
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
