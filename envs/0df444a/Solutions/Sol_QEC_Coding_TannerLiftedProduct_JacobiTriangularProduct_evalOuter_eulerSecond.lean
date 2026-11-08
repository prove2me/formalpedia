-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.evalOuter_eulerSecond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:34:45.07905+00:00
-- url     : https://prove2.me/submissions/03ada0b7-c00a-4769-a2c9-119b00002df0

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.Topology.WithTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_continuous_evalOuter
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_summable_eulerSecondTerm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiGeneralCore_FormalPowerSeries_euler_second_identity


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
theorem _root_.solution (a : Outer) :
    evalOuter (qPochhammerInf (-a)) =
      ∑' k : ℕ, evalOuter
        ((PowerSeries.X : Outer) ^ k.choose 2 * a ^ k *
          qPochhammerInv (R := DiscreteTarget) k) := by
  rw [euler_second_identity a]
  exact (summable_eulerSecondTerm a).map_tsum
    evalOuter continuous_evalOuter
end QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct
