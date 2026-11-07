-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledProjection_tendsto_codiscrete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:04:04.770833+00:00
-- url     : https://prove2.me/submissions/b67a29a4-98e7-4d04-ba97-61b805088b0e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicDifferentiation
import Mathlib.LinearAlgebra.Isomorphisms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_interior_openEmbedding
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



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
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) :
    letI := lpsOriginalFilledTopology N
    Tendsto (fun z : ℂ => lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z))
      (Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet)
      (Filter.codiscrete (LPSOriginalFilledCurve N)) := by
  let := lpsOriginalFilledTopology N
  rw [Filter.tendsto_def]
  intro s hs
  change {z : ℂ | lpsOriginalHolomorphicCovectorProjection N (UpperHalfPlane.ofComplex z) ∈ s} ∈
    Filter.codiscreteWithin UpperHalfPlane.upperHalfPlaneSet
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro z hz
  let π := lpsOriginalHolomorphicCovectorProjection N
  have hπ : IsLocalHomeomorph π :=
    (lpsOriginalFilledTopology_interior_openEmbedding N).isLocalHomeomorph.comp
      (lpsGamma0_quotient_localHomeomorph N hN)
  have hsource : z ∈ UpperHalfPlane.ofComplex.source := by
    change z ∈ (UpperHalfPlane.isOpenEmbedding_coe.toOpenPartialHomeomorph
      (UpperHalfPlane.coe : ℍ → ℂ)).target
    rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨⟨z,hz⟩,rfl⟩
  have ho : Tendsto UpperHalfPlane.ofComplex (𝓝[≠] z)
      (𝓝[≠] (UpperHalfPlane.ofComplex z)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(UpperHalfPlane.ofComplex.continuousAt hsource).tendsto.mono_left nhdsWithin_le_nhds,
        UpperHalfPlane.ofComplex.eventually_ne_nhdsWithin hsource⟩
  have ht := (lpsOriginalLocalHomeomorph_tendsto_punctured hπ
    (UpperHalfPlane.ofComplex z)).comp ho
  have hf : ∀ᶠ y in 𝓝[≠] (π (UpperHalfPlane.ofComplex z)), y ∈ s := by
    have hh := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hs
      (π (UpperHalfPlane.ofComplex z)) (Set.mem_univ _)
    simp only [Set.compl_univ,Set.union_empty] at hh
    exact hh
  filter_upwards [ht.eventually hf] with w hw
  exact Or.inl hw
end QEC.Coding.TannerLiftedProduct
