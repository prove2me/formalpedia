-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.map_cyclicAlgebraRegularNorm_eq_splitReducedNorm_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:51:16.980968+00:00
-- url     : https://prove2.me/submissions/07aacb27-536e-4847-b34a-b837fbb80da5

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_GlobalNormOneBridge
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_SplittingFieldDescent
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm
import Mathlib.Algebra.Polynomial.Roots
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_IntrinsicNorm
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_splittingCyclicScalarExtension_regularNorm_eq_splitReducedNorm_pow
import Theorems.Thm_Algebra_norm_tensorProduct_includeRight


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped Polynomial
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u : (CyclicAlgebra P r)ˣ) :
    algebraMap (FunctionField P) (SplittingFunctionField P r)
        (cyclicAlgebraRegularNorm P r (u : CyclicAlgebra P r)) =
      ((cyclicAlgebraSplitReducedNorm P r u :
          (SplittingFunctionField P r)ˣ) :
        SplittingFunctionField P r) ^ r.matrixRank := by
  calc
    algebraMap (FunctionField P) (SplittingFunctionField P r)
        (cyclicAlgebraRegularNorm P r (u : CyclicAlgebra P r)) =
      Algebra.norm (SplittingFunctionField P r)
        (Algebra.TensorProduct.includeRight
          (R := FunctionField P) (A := SplittingFunctionField P r)
          (B := CyclicAlgebra P r) (u : CyclicAlgebra P r)) := by
      exact (Algebra.norm_tensorProduct_includeRight
        (functionFieldCyclicBasis P r) (u : CyclicAlgebra P r)).symm
    _ = _ :=
      splittingCyclicScalarExtension_regularNorm_eq_splitReducedNorm_pow
        P r u
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
