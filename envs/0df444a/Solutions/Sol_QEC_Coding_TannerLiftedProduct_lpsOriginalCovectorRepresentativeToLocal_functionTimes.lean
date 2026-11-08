-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCovectorRepresentativeToLocal_functionTimes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:29:19.691985+00:00
-- url     : https://prove2.me/submissions/c75d3859-518c-442a-af8c-e12508f52e14

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalRegularDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeLocalDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms Filter Topology
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) (x : LPSOriginalFilledCurve N)
local notation "a" => lpsOriginalLocalChartCenter N hN x
local notation "G" => MeromorphicGermRing a
local notation "Cov" => LPSOriginalFilledMeromorphicCovectorRepresentatives N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_26
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_a8e2bd7548_28
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (F : LPSOriginalFilledMeromorphicFunctionRing N hN) (σ : Cov) :
    lpsOriginalCovectorRepresentativeToLocal N hN x
      (lpsOriginalFilledMeromorphicFunctionTimesCovector N hN F σ) =
      lpsOriginalRepresentativeToLocal N hN x F *
        lpsOriginalCovectorRepresentativeToLocal N hN x σ := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  apply Subtype.ext
  apply Germ.coe_eq.mpr
  filter_upwards with z
  exact lpsOriginalFilledFunctionTimesCovector_chart N hN F.val σ.val x z
end QEC.Coding.TannerLiftedProduct
