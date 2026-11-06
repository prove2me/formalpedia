-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge.scaled_coordinates_mem_windowCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:30:43.580903+00:00
-- url     : https://prove2.me/submissions/87b7dd65-9aaa-42b6-9e4b-2b1a503f9dd3

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
    [IsScalarTower k (RatFunc k) F] [Fintype ι]
    (b : Module.Basis ι (RatFunc k) F) (a d : Polynomial k) (x : F)
    (hcoordinate : ∀ j : ι,
      twoChartScaledCoordinateMap b a d x j ∈
        directLaurentWindow k (-(d.natDegree : ℤ)) (a.natDegree : ℤ)) :
    twoChartScaledCoordinateMap b a d x ∈
      directLaurentWindowCoordinates k ι (-(d.natDegree : ℤ)) (a.natDegree : ℤ) := by
  classical
  let lift : ι →₀ directLaurentWindow k (-(d.natDegree : ℤ)) (a.natDegree : ℤ) :=
    (Finsupp.linearEquivFunOnFinite k
      (directLaurentWindow k (-(d.natDegree : ℤ)) (a.natDegree : ℤ)) ι).symm
      (fun j => ⟨twoChartScaledCoordinateMap b a d x j, hcoordinate j⟩)
  refine ⟨lift, ?_⟩
  ext j
  simp [lift, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
end QEC.Coding.AlgebraicGeometry.TwoChartFiniteDimensionalBridge
