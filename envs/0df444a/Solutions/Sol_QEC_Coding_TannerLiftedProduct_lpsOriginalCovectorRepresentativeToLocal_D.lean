-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCovectorRepresentativeToLocal_D
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:27:23.975312+00:00
-- url     : https://prove2.me/submissions/1e21a365-4c3b-46e7-8c83-f595b08d3947

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
    (F : LPSOriginalFilledMeromorphicFunctionRing N hN) :
    lpsOriginalCovectorRepresentativeToLocal N hN x
      ⟨lpsOriginalFilledFunctionCovector N hN F.val,
        lpsOriginalFilledFunctionCovector_meromorphic N hN F.val F.property⟩ =
      germDerivative a (lpsOriginalRepresentativeToLocal N hN x F) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let e := lpsOriginalLocalChart N hN x
  have ha : a ∈ e.target := e.map_source (lpsOriginalLocalChart_mem_source N hN x)
  apply Subtype.ext
  change (lpsOriginalFilledCovectorChartCoefficient N hN
    (lpsOriginalFilledFunctionCovector N hN F.val) x : Germ (𝓝[≠] a) ℂ) = _
  rw [germDerivative_value a (lpsOriginalRepresentativeToLocal N hN x F)
    (F.val ∘ e.symm) (F.property x a ha) rfl]
  apply Germ.coe_eq.mpr
  filter_upwards [nhdsWithin_le_nhds (e.open_target.mem_nhds ha)] with z hz
  exact lpsOriginalFilledFunctionCovector_chart N hN F.val x z hz
end QEC.Coding.TannerLiftedProduct
