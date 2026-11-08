-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledCovector_chart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:37:19.407206+00:00
-- url     : https://prove2.me/submissions/287d6957-8c5d-4ed1-a715-50f91dfe3bb9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorCoordinates
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorNormalForm
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledCovector_inCoordinates
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_normalizedGermValue_on
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (hmer : lpsOriginalFilledCovectorChartMeromorphic N hN sigma)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z ∈ (chartAt ℂ x).target) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    lpsOriginalFilledCovectorChartCoefficient N hN (lpsOriginalNormalizedFilledCovector N hN sigma)
      x z = toMeromorphicNFOn (lpsOriginalFilledCovectorChartCoefficient N hN sigma x)
        (chartAt ℂ x).target z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  unfold lpsOriginalFilledCovectorChartCoefficient
  rw [lpsOriginalNormalizedFilledCovector_inCoordinates N hN sigma hmer x
    ((chartAt ℂ x).symm z) ((chartAt ℂ x).map_target hz),
    (chartAt ℂ x).right_inv hz]
  change toMeromorphicNFAt (lpsOriginalFilledCovectorChartCoefficient N hN sigma x) z z * 1 = _
  rw [mul_one]
  exact (normalizedGermValue_on _ _ z (hmer x) hz).symm
end QEC.Coding.TannerLiftedProduct
