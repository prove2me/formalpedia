-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraRegularNorm_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:50:55.646014+00:00
-- url     : https://prove2.me/submissions/28722a56-3b36-4a97-993e-af9a8e5a653d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_finrank_cyclicAlgebra


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (a : FunctionField P) :
    cyclicAlgebraRegularNorm P r
        (algebraMap (FunctionField P) (CyclicAlgebra P r) a) =
      a ^ (r.matrixRank * r.matrixRank) := by
  change Algebra.norm (FunctionField P)
      (algebraMap (FunctionField P) (CyclicAlgebra P r) a) = _
  rw [Algebra.norm_algebraMap, finrank_cyclicAlgebra]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
