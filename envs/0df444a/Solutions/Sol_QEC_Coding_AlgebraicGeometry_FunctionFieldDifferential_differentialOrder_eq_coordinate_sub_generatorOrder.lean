-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential.differentialOrder_eq_coordinate_sub_generatorOrder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:23:58.916634+00:00
-- url     : https://prove2.me/submissions/e774f906-1b2d-44b2-9b79-e94d657fecc1

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_DifferentialLocal
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_CanonicalDifferential

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
open scoped RatFunc
variable {k F : Type*} [Field k] [Finite k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [Algebra.IsSeparable (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
namespace QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
theorem _root_.solution (P : GlobalPlace k F)
    (omega : Differential k F) (homega : omega ≠ 0) {a : F}
    (ha : IsLocalDerivativeLatticePrincipalCutoff (k := k) (F := F) P a) :
    differentialOrder (k := k) (F := F) P omega homega =
      P.order (functionFieldDifferentialCoordinate (k := k) (F := F) omega) -
        P.order a := by
  unfold differentialOrder
  rw [localDerivativeLatticeGeneratorOrder_eq_order (k := k) (F := F) P ha]
end QEC.Coding.AlgebraicGeometry.FunctionFieldDifferential
