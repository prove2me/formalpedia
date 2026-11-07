-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJComplexDerivative_eventually_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:12:46.164906+00:00
-- url     : https://prove2.me/submissions/28e97cb2-98d7-4dda-a562-6f0dbb6fcda7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_ofComplex_analytic


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
theorem _root_.solution :
    ∀ᶠ z in Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet,
      deriv (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex) z ≠ 0 := by
  change {z | deriv (lpsOriginalJInvariant ∘ UpperHalfPlane.ofComplex) z ≠ 0} ∈
    Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro z hz
  have hm := (lpsOriginalJInvariant_ofComplex_analytic (⟨z,hz⟩ : ℍ)).meromorphicAt.deriv
  have he := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hm).mp
    (lpsOriginalJComplexDerivative_order_ne_top z hz)
  filter_upwards [he] with w hw
  exact Or.inl hw
end QEC.Coding.TannerLiftedProduct
