-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.twoChartScaledCoordinateMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:30:57.691319+00:00
-- url     : https://prove2.me/submissions/cfe78132-3b12-4f40-a29d-b4b0ed5c5b4b

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
    (b : Module.Basis ι (RatFunc k) F) {a d : Polynomial k} (ha : a ≠ 0) (hd : d ≠ 0) :
    Function.Injective (twoChartScaledCoordinateMap b a d) := by
  have haK : algebraMap (Polynomial k) (RatFunc k) a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) (RatFunc k))).mpr ha
  have hdK : algebraMap (Polynomial k) (RatFunc k) d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) (RatFunc k))).mpr hd
  have hc : algebraMap (Polynomial k) (RatFunc k) a *
      InverseAffinePlace.rationalInvolution k
        (algebraMap (Polynomial k) (RatFunc k) d) ≠ 0 :=
    mul_ne_zero haK
      ((map_ne_zero_iff _ (InverseAffinePlace.rationalInvolution k).injective).mpr hdK)
  intro x y hxy
  apply b.repr.injective
  ext j
  have hj := congrArg (fun c : ι →₀ RatFunc k => c j) hxy
  change (algebraMap (Polynomial k) (RatFunc k) a *
      InverseAffinePlace.rationalInvolution k
        (algebraMap (Polynomial k) (RatFunc k) d)) * b.repr x j =
    (algebraMap (Polynomial k) (RatFunc k) a *
      InverseAffinePlace.rationalInvolution k
        (algebraMap (Polynomial k) (RatFunc k) d)) * b.repr y j at hj
  exact mul_left_cancel₀ hc hj
end QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
