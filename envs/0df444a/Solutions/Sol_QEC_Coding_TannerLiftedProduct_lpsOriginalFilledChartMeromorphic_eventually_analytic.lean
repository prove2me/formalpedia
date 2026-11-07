-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledChartMeromorphic_eventually_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:31:48.748194+00:00
-- url     : https://prove2.me/submissions/f1eab812-4286-412d-953c-352e374a72e8

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicRestriction
import Mathlib.Analysis.Analytic.Polynomial
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicPoleClearing
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold
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
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (x : LPSOriginalFilledCurve N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    ∀ᶠ y in 𝓝[≠] x, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω F y := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let e := chartAt ℂ x
  have hx : x ∈ e.source := mem_chart_source ℂ x
  have hm := hF x (e x) (e.map_source hx)
  have ht : Tendsto e (𝓝[≠] x) (𝓝[≠] (e x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨(e.continuousAt hx).tendsto.mono_left
      nhdsWithin_le_nhds,e.eventually_ne_nhdsWithin hx⟩
  have ha := ht.eventually hm.eventually_analyticAt
  have hs : ∀ᶠ y in 𝓝[≠] x, y ∈ e.source :=
    nhdsWithin_le_nhds (e.open_source.mem_nhds hx)
  filter_upwards [ha,hs] with y hy hys
  apply (contMDiffAt_iff_source_of_mem_source
    (I := 𝓘(ℂ)) (I' := 𝓘(ℂ)) (n := ω) (x := x) hys).mpr
  rw [contMDiffWithinAt_iff_contDiffWithinAt]
  simpa only [extChartAt_coe_symm,extChartAt_coe,modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm,Set.range_id,Function.comp_def,id_eq]
    using hy.contDiffAt.contDiffWithinAt
end QEC.Coding.TannerLiftedProduct
