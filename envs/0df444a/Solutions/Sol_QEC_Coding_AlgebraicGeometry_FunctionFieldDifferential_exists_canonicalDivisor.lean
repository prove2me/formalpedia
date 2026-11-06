-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.exists_canonicalDivisor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:28:40.407347+00:00
-- url     : https://prove2.me/submissions/2e87d69a-e620-4b78-847a-5f554d96de83

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_differentialDivisor_isCanonical
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution :
    ∃ K : Divisor (GlobalPlace k F), IsCanonicalDivisor (k := k) (F := F) K := by
  exact ⟨differentialDivisor (k := k) (F := F)
      (functionFieldDifferentialGenerator (k := k) (F := F))
      (functionFieldDifferentialGenerator_ne_zero (k := k) (F := F)),
    differentialDivisor_isCanonical (k := k) (F := F)
      (functionFieldDifferentialGenerator (k := k) (F := F))
      (functionFieldDifferentialGenerator_ne_zero (k := k) (F := F))⟩
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
