-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicCovectorToClass_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:01:00.954829+00:00
-- url     : https://prove2.me/submissions/e8136f55-f4d1-4252-8db9-5f22709caa12

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorCoordinates
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicNativeCovectors
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    Function.Injective (lpsOriginalHolomorphicCovectorToClassLinearMap N hN) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro sigma tau he
  apply ContMDiffSection.ext
  intro x
  have hg := congrArg (lpsOriginalNativeCovectorToLocal N hN x) he
  change lpsOriginalCovectorRepresentativeToLocal N hN x
      (lpsOriginalHolomorphicCovectorToMeromorphicLinearMap N hN sigma) =
      lpsOriginalCovectorRepresentativeToLocal N hN x
        (lpsOriginalHolomorphicCovectorToMeromorphicLinearMap N hN tau) at hg
  have hpunctured := Filter.Germ.coe_eq.mp (congrArg Subtype.val hg)
  have hvalues := analytic_value_eq_of_punctured_germ
    (lpsOriginalHolomorphicCovectorChartCoefficient_analytic N hN sigma x)
    (lpsOriginalHolomorphicCovectorChartCoefficient_analytic N hN tau x) hpunctured
  apply ContinuousLinearMap.ext
  intro v
  rw [lpsOriginalHolomorphicCovectorChart_evaluate N hN sigma x x v (mem_chart_source ℂ x),
    lpsOriginalHolomorphicCovectorChart_evaluate N hN tau x x v (mem_chart_source ℂ x), hvalues]
end QEC.Coding.TannerLiftedProduct
