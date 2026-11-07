-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_isManifold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:29:34.402932+00:00
-- url     : https://prove2.me/submissions/f7d024e9-e115-4909-a5e7-d303bec19d19

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspAnalytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_interior_cusp_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_cusp_interior_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_cusp_cusp_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Quotient_isManifold
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
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
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    IsManifold 𝓘(ℂ) ω (LPSOriginalFilledCurve N) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  apply isManifold_of_contDiffOn 𝓘(ℂ) ω (LPSOriginalFilledCurve N)
  intro a b ha hb
  change a∈Set.range (lpsOriginalFilledInteriorChart N hN) ∪
    Set.range (lpsOriginalFilledCuspChart N) at ha
  change b∈Set.range (lpsOriginalFilledInteriorChart N hN) ∪
    Set.range (lpsOriginalFilledCuspChart N) at hb
  rcases ha with ⟨x,rfl⟩|⟨c,rfl⟩ <;> rcases hb with ⟨y,rfl⟩|⟨d,rfl⟩
  · let := lpsGamma0QuotientChartedSpace N hN
    let := lpsGamma0Quotient_isManifold N hN
    have hc := IsManifold.compatible_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ)) (n:=ω) x)
      (IsManifold.chart_mem_maximalAtlas (I:=𝓘(ℂ)) (n:=ω) y)
    have hf := (mem_groupoid_of_pregroupoid.mpr hc).1
    simpa only [lpsOriginalFilledInteriorChart,
      OpenPartialHomeomorph.lift_openEmbedding_trans,contDiffPregroupoid] using hf
  · intro z hz
    have ht := (lpsOriginalFilled_interior_cusp_analytic N hN x d z hz.1).1
    simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
      Function.comp_def,id_eq] using ht.contDiffAt (n:=ω) |>.contDiffWithinAt
  · intro z hz
    have ht := lpsOriginalFilled_cusp_interior_analytic N hN y c z hz.1
    simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
      Function.comp_def,id_eq] using ht.contDiffAt (n:=ω) |>.contDiffWithinAt
  · intro z hz
    have ht := lpsOriginalFilled_cusp_cusp_analytic N c d z hz.1
    simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
      Function.comp_def,id_eq] using ht.contDiffAt (n:=ω) |>.contDiffWithinAt
end QEC.Coding.TannerLiftedProduct
