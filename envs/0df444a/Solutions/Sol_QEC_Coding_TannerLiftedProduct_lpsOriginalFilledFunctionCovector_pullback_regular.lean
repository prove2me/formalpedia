-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledFunctionCovector_pullback_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:07:21.631622+00:00
-- url     : https://prove2.me/submissions/e03dcf05-f17b-42a9-a314-140eefdbe118

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
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
        (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z))) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    lpsOriginalFilledFunctionCovector N hN F
      (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z))
      (mfderiv 𝓘(ℂ) 𝓘(ℂ)
        (fun w : ℂ => lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex w))
          z (1 : ℂ)) = deriv (lpsOriginalFilledMeromorphicPullback N F) z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let p : ℂ → LPSOriginalFilledCurve N :=
    fun w => lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex w)
  let y := p z
  let A : ℂ →L[ℂ] ℂ := lpsOriginalFilledFunctionCovector N hN F y
  let B : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) p z
  have hp : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) p z :=
    ((lpsOriginalHolomorphicCovectorProjection_contMDiff N hN
      (UpperHalfPlane.ofComplex z)).mdifferentiableAt (by decide)).comp z
        (UpperHalfPlane.mdifferentiableAt_ofComplex hz)
  have hmaps : (mfderiv 𝓘(ℂ) 𝓘(ℂ) (F ∘ p) z : ℂ →L[ℂ] ℂ) = A.comp B :=
    mfderiv_comp z hF hp
  rw [mfderiv_eq_fderiv] at hmaps
  have he := congrArg (fun linearMap : ℂ →L[ℂ] ℂ => linearMap (1 : ℂ)) hmaps
  change deriv (lpsOriginalFilledMeromorphicPullback N F) z = A (B (1 : ℂ)) at he
  exact he.symm
end QEC.Coding.TannerLiftedProduct
