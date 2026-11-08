-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNativeCovectorToLocal_class
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:27:22.409846+00:00
-- url     : https://prove2.me/submissions/36bf9d18-e188-435a-89c5-a609acb79f68

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalRegularDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGenericCompactDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeLocalDifferentialComparison

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
theorem _root_.solution (σ : Cov) :
    lpsOriginalNativeCovectorToLocal N hN x (lpsOriginalCompactMeromorphicCovectorClass N hN σ) =
      lpsOriginalCovectorRepresentativeToLocal N hN x σ := rfl
end QEC.Coding.TannerLiftedProduct
