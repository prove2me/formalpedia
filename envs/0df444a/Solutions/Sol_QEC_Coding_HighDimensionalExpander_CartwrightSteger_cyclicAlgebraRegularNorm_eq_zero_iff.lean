-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.cyclicAlgebraRegularNorm_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:50:58.841211+00:00
-- url     : https://prove2.me/submissions/183bab34-b958-4b6f-b50b-c2c873df5c5e

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
    cyclicAlgebraRegularNorm P r x = 0 ↔ x = 0 := by
  letI : IsDomain (CyclicAlgebra P r) := cyclicAlgebraIsDomain P r
  exact Algebra.norm_eq_zero_iff_of_basis (functionFieldCyclicBasis P r)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
