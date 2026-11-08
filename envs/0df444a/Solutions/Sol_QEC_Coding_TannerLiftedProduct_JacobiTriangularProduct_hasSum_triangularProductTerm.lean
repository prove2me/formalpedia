-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct.hasSum_triangularProductTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:54:50.293409+00:00
-- url     : https://prove2.me/submissions/3603b65a-3ccc-40d6-86bf-a2a5b0d69e2d

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeProduct
import Mathlib.RingTheory.PowerSeries.Evaluation
import Mathlib.Topology.WithTopology
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTriangularProduct
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_hasSum_triangularEulerLeft
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_hasSum_triangularEulerRight
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTriangularProduct_summable_triangularProductTerm

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
    HasSum triangularProductTerm
      ((evaluatedPochhammerInf * evalOuter (qPochhammerInf (-sourceQ))) *
        evalOuter (qPochhammerInf (-sourceOne))) := by
  have h :
      (evaluatedPochhammerInf * evalOuter (qPochhammerInf (-sourceQ))) *
          evalOuter (qPochhammerInf (-sourceOne)) =
        ∑' p : ℕ × ℕ, triangularProductTerm p := by
    exact hasSum_triangularEulerLeft.mul_eq hasSum_triangularEulerRight
      summable_triangularProductTerm.hasSum
  rw [h]
  exact summable_triangularProductTerm.hasSum
end QEC.Coding.TannerLiftedProduct.JacobiTriangularProduct
