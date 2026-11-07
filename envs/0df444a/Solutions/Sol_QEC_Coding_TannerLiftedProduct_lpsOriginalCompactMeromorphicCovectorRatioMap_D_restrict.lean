-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCompactMeromorphicCovectorRatioMap_D_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:56:52.013319+00:00
-- url     : https://prove2.me/submissions/d15c3728-a424-4b1a-bf5c-8a12ab6aaa9b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledMeromorphicPullback_eventually_regular
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJComplexDerivative_eventually_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledFunctionCovectorRatio_pullback_regular
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold


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
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (F : R) :
    (lpsOriginalCompactToRestrictedMeromorphic N hN
      (lpsOriginalCompactMeromorphicCovectorRatioMap N hN
        ⟨lpsOriginalFilledFunctionCovector N hN F.val,
          lpsOriginalFilledFunctionCovector_meromorphic N hN F.val F.property⟩)).val *
      lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
        (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic) =
      lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
        (lpsOriginalFilledMeromorphicRestriction N hN F.val F.property).val := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let G : R := ⟨lpsOriginalFilledCovectorRatio N hN
    (lpsOriginalFilledFunctionCovector N hN F.val)
    (lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N)),
      lpsOriginalFilledCovectorRatio_meromorphic N hN _ _
        (lpsOriginalFilledFunctionCovector_meromorphic N hN F.val F.property)
        (lpsOriginalFilledFunctionCovector_meromorphic N hN (lpsOriginalFilledJ N)
          (lpsOriginalFilledChartMeromorphic_j N hN))⟩
  change (lpsOriginalCompactToRestrictedMeromorphic N hN
    ((lpsOriginalCompactMeromorphicGermMap N hN).rangeRestrict G)).val * _ = _
  rw [lpsOriginalCompactToRestrictedMeromorphic_apply]
  apply Subtype.ext
  change ((lpsOriginalFilledMeromorphicPullback N G.val :
    Filter.Germ (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet) ℂ) *
    (lpsOriginalMeromorphicGermCoefficientDerivative UpperHalfPlane.upperHalfPlaneSet
      (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic)).val) = _
  rw [lpsOriginalMeromorphicGermCoefficientDerivative_value UpperHalfPlane.upperHalfPlaneSet
    (lpsOriginalHolomorphicToMeromorphicGerm lpsOriginalJHolomorphic)
    (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex)
    (lpsOriginalHolomorphic_ofComplex_meromorphic lpsOriginalJHolomorphic) rfl]
  rw [lpsOriginalMeromorphicGermCoefficientDerivative_value UpperHalfPlane.upperHalfPlaneSet
    (lpsOriginalFilledMeromorphicRestriction N hN F.val F.property).val
    (lpsOriginalFilledMeromorphicPullback N F.val)
    (lpsOriginalFilledMeromorphicPullback_meromorphic N hN F.val F.property) rfl]
  rw [←Filter.Germ.coe_mul]
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [lpsOriginalFilledMeromorphicPullback_eventually_regular N hN F.val F.property,
    lpsOriginalFilledMeromorphicPullback_eventually_regular N hN (lpsOriginalFilledJ N)
      (lpsOriginalFilledChartMeromorphic_j N hN),
    lpsOriginalJComplexDerivative_eventually_ne_zero,
    Filter.self_mem_codiscreteWithin UpperHalfPlane.upperHalfPlaneSet] with z hF hJ hj hz
  have he := lpsOriginalFilledFunctionCovectorRatio_pullback_regular N hN F.val z hz
    (hF.mdifferentiableAt (by decide)) (hJ.mdifferentiableAt (by decide)) hj
  change lpsOriginalFilledMeromorphicPullback N G.val z *
    deriv (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex) z =
      deriv (lpsOriginalFilledMeromorphicPullback N F.val) z
  rw [he]
  exact div_mul_cancel₀ _ hj
end QEC.Coding.TannerLiftedProduct
