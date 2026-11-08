-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphicCovectorRatioMap_dj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:28:37.495203+00:00
-- url     : https://prove2.me/submissions/b9f4e78c-4722-441b-9204-2602ac244866

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology
open scoped UpperHalfPlane Manifold
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
local notation "R" => LPSOriginalFilledMeromorphicFunctionRing N hN
local notation "L" => LPSOriginalCompactMeromorphicGermRing N hN
local notation "V" => LPSOriginalFilledMeromorphicCovectorRepresentatives N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_391f8f7aa3_629
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_391f8f7aa3_630
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    lpsOriginalCompactMeromorphicCovectorRatioMap N hN
      ⟨lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N),
        lpsOriginalFilledFunctionCovector_meromorphic N hN (lpsOriginalFilledJ N)
          (lpsOriginalFilledChartMeromorphic_j N hN)⟩ = 1 := by
  let := lpsOriginalFilledTopology N
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [lpsOriginalFilledJCovector_eventually_ne_zero N hN] with y hy
  change lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ) /
    lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y (1 : ℂ) = 1
  exact div_self hy
end QEC.Coding.TannerLiftedProduct
