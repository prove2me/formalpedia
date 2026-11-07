-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledMeromorphicPullback_eventually_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:07:17.08306+00:00
-- url     : https://prove2.me/submissions/4b07ca9c-c8c1-4710-ae7b-3380fc9bcd60

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledProjection_tendsto_codiscrete
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledChartMeromorphic_finite_nonanalytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_t2Space


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
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    ∀ᶠ z in Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet,
      ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F
        (lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z)) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let : T1Space (LPSOriginalFilledCurve N) := @T2Space.t1Space _
    (lpsOriginalFilledTopology N) (lpsOriginalFilledTopology_t2Space N)
  have he := (lpsOriginalFilledChartMeromorphic_finite_nonanalytic N hN F hF).compl_mem_codiscrete
  have hp := (lpsOriginalFilledProjection_tendsto_codiscrete N hN).eventually he
  filter_upwards [hp] with z hz
  exact not_not.mp hz
end QEC.Coding.TannerLiftedProduct
