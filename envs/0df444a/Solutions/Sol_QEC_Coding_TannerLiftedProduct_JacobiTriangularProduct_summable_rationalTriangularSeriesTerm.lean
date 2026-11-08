-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.summable_rationalTriangularSeriesTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:57:36.742046+00:00
-- url     : https://prove2.me/submissions/b3e888bb-c6ae-4fa2-aa48-5685bd1deeec

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.Topology.WithTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_continuous_mapToRat
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_summable_evaluatedTriangularSeriesTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_mapToRat_triangularSeriesTerm

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
    Summable (fun n : ℕ =>
      (PowerSeries.X : PowerSeries ℚ) ^ (n * (n + 1))) := by
  have h := summable_evaluatedTriangularSeriesTerm.map
    mapToRat continuous_mapToRat
  apply h.congr
  intro n
  exact mapToRat_triangularSeriesTerm n
end QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct
