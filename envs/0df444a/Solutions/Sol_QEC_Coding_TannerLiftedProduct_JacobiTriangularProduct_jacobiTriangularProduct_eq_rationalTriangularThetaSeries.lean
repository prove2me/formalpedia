-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.jacobiTriangularProduct_eq_rationalTriangularThetaSeries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:04:39.980983+00:00
-- url     : https://prove2.me/submissions/554d04e1-1f0b-481e-ad41-9c8b4691c2f1

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.Topology.WithTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_evaluatedTriangularProduct_eq_series
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_mapToRat_evaluatedTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_mapToRat_evaluatedTriangularSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_rationalUnilateralTriangularSeries_eq_theta

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
    jacobiTriangularProduct = rationalTriangularThetaSeries := by
  calc
    jacobiTriangularProduct = mapToRat evaluatedTriangularProduct :=
      mapToRat_evaluatedTriangularProduct.symm
    _ = mapToRat evaluatedTriangularSeries :=
      congrArg mapToRat evaluatedTriangularProduct_eq_series
    _ = ∑' n : ℕ,
        (PowerSeries.X : PowerSeries ℚ) ^ (n * (n + 1)) :=
      mapToRat_evaluatedTriangularSeries
    _ = rationalTriangularThetaSeries :=
      rationalUnilateralTriangularSeries_eq_theta
end QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct
