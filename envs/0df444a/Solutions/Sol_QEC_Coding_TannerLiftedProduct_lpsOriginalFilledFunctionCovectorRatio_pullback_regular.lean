-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledFunctionCovectorRatio_pullback_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:12:47.777627+00:00
-- url     : https://prove2.me/submissions/9d9ca4db-ff59-457a-8769-b09efcab188b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledFunctionCovector_pullback_regular
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
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ) (z : ℂ) (hz : 0 < z.im)
    (hF : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F
        (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z)))
    (hJ : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalFilledJ N)
        (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z)))
    (hj : deriv (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex) z ≠ 0) :
    lpsOriginalFilledMeromorphicPullback N
      (lpsOriginalFilledCovectorRatio N hN
        (lpsOriginalFilledFunctionCovector N hN F)
        (lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N))) z =
      deriv (lpsOriginalFilledMeromorphicPullback N F) z /
        deriv (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex) z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let p : ℂ → LPSOriginalFilledCurve N :=
    fun w => lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex w)
  let y := p z
  let a : ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) p z (1 : ℂ)
  let A : ℂ →L[ℂ] ℂ := lpsOriginalFilledFunctionCovector N hN F y
  let B : ℂ →L[ℂ] ℂ := lpsOriginalFilledFunctionCovector N hN (lpsOriginalFilledJ N) y
  have hA : A a = deriv (lpsOriginalFilledMeromorphicPullback N F) z :=
    lpsOriginalFilledFunctionCovector_pullback_regular N hN F z hz hF
  have hB : B a = deriv (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex) z :=
    lpsOriginalFilledFunctionCovector_pullback_regular N hN (lpsOriginalFilledJ N) z hz hJ
  have ha : a ≠ 0 := by
    intro ha0
    rw [ha0,map_zero] at hB
    exact hj hB.symm
  have hAs := A.map_smul a (1 : ℂ)
  have hBs := B.map_smul a (1 : ℂ)
  change A (a * 1) = a * A (1 : ℂ) at hAs
  change B (a * 1) = a * B (1 : ℂ) at hBs
  rw [mul_one] at hAs hBs
  change A (1 : ℂ) / B (1 : ℂ) = _
  rw [←hA,←hB,hAs,hBs]
  exact (mul_div_mul_left _ _ ha).symm
end QEC.Coding.TannerLiftedProduct
