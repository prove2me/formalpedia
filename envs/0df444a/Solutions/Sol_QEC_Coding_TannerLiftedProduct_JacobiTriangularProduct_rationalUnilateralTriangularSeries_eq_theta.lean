-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.rationalUnilateralTriangularSeries_eq_theta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:01:38.485227+00:00
-- url     : https://prove2.me/submissions/342df891-5233-43d0-9bff-74262824be0c

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.Topology.WithTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_card_integerTriangularRoots_eq_two_mul_natural
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_coeff_rationalUnilateralTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_rationalTriangularThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_rationalTriangularThetaSeries



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter PowerSeries
open scoped PowerSeries.WithPiTopology Topology
open QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct
open JacobiGeneralCore.FormalPowerSeries
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteRatUniformSpace
attribute [local instance] discreteRatUniformSpace
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteRatTopologicalSpace
attribute [local instance] discreteRatTopologicalSpace
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteRatUniformity
attribute [local instance] discreteRatUniformity
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteRatTopology
attribute [local instance] discreteRatTopology
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteTargetUniformSpace
attribute [local instance] discreteTargetUniformSpace
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteTargetTopologicalSpace
attribute [local instance] discreteTargetTopologicalSpace
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteTargetUniformity
attribute [local instance] discreteTargetUniformity
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.discreteTargetTopology
attribute [local instance] discreteTargetTopology
namespace QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct
theorem _root_.solution :
    (∑' n : ℕ,
        (PowerSeries.X : PowerSeries ℚ) ^ (n * (n + 1))) =
      rationalTriangularThetaSeries := by
  ext d
  rw [coeff_rationalUnilateralTriangularSeries,
    coeff_rationalTriangularThetaSeries,
    card_integerTriangularRoots_eq_two_mul_natural]
  push_cast
  ring
end QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct
