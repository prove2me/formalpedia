-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.twoChartScaledCoordinateMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:29:37.717886+00:00
-- url     : https://prove2.me/submissions/eff47745-8bbd-45f6-820d-76467a4c0798

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_DirectChartCommonDenominator
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseAffinePlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_InverseChartDenominatorTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_LaurentFiniteWindow
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_TwoChartFiniteDimensionalBridge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
open scoped LaurentPolynomial Polynomial RatFunc
variable {k F ι : Type*}
namespace QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
theorem _root_.solution
    [Field k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F]
    (b : Module.Basis ι (RatFunc k) F) (a d : Polynomial k) (x : F) (j : ι) :
    twoChartScaledCoordinateMap b a d x j =
      (algebraMap (Polynomial k) (RatFunc k) a *
        InverseAffinePlace.rationalInvolution k
          (algebraMap (Polynomial k) (RatFunc k) d)) *
        b.repr x j := rfl
end QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
