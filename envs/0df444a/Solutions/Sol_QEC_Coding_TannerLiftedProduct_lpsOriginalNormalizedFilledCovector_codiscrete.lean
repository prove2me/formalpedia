-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledCovector_codiscrete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:47:30.027248+00:00
-- url     : https://prove2.me/submissions/9ede8045-714a-4f13-901d-8847d61bacc0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeHolomorphicExtension
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNormalizedFilledCovector_chart
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
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (hmer : lpsOriginalFilledCovectorChartMeromorphic N hN sigma) :
    letI := lpsOriginalFilledTopology N
    ∀ᶠ y in Filter.codiscrete (LPSOriginalFilledCurve N),
      sigma y = lpsOriginalNormalizedFilledCovector N hN sigma y := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  change {y | sigma y = lpsOriginalNormalizedFilledCovector N hN sigma y} ∈
    Filter.codiscreteWithin (Set.univ : Set (LPSOriginalFilledCurve N))
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  intro x hx
  simp only [Set.compl_univ, Set.union_empty]
  let e := chartAt ℂ x
  let f := lpsOriginalFilledCovectorChartCoefficient N hN sigma x
  have hs : x ∈ e.source := mem_chart_source ℂ x
  have ht : Tendsto e (𝓝[≠] x) (𝓝[≠] (e x)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨(e.continuousAt hs).tendsto.mono_left nhdsWithin_le_nhds,
        e.eventually_ne_nhdsWithin hs⟩
  have hf := ht.eventually ((hmer x).toMeromorphicNFOn_eq_self_on_nhdsNE
    (e.map_source hs))
  filter_upwards [hf, nhdsWithin_le_nhds (e.open_source.mem_nhds hs)] with y hy hys
  have hc := lpsOriginalNormalizedFilledCovector_chart N hN sigma hmer x (e y)
    (e.map_source hys)
  change lpsOriginalFilledCovectorChartCoefficient N hN
    (lpsOriginalNormalizedFilledCovector N hN sigma) x (e y) =
      toMeromorphicNFOn f e.target (e y) at hc
  change toMeromorphicNFOn f e.target (e y) = f (e y) at hy
  have heq : lpsOriginalFilledCovectorChartCoefficient N hN
      (lpsOriginalNormalizedFilledCovector N hN sigma) x (e y) = f (e y) := hc.trans hy
  apply ContinuousLinearMap.ext
  intro v
  rw [lpsOriginalFilledCovectorChart_evaluate N hN sigma x y v hys,
    lpsOriginalFilledCovectorChart_evaluate N hN
      (lpsOriginalNormalizedFilledCovector N hN sigma) x y v hys, heq]
end QEC.Coding.TannerLiftedProduct
