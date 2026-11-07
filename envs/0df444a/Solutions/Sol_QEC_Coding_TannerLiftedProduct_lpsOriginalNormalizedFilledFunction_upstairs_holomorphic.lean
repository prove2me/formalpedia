-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNormalizedFilledFunction_upstairs_holomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:15:56.878601+00:00
-- url     : https://prove2.me/submissions/b0f0384a-54b1-492d-8702-35a804581a13

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_MeromorphicManifoldNormalForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCompactMeromorphicDifferentialComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizedIntegral
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_MeromorphicGerms_chartNormalizedMeromorphicFunction_analyticAt
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
open QEC.Coding.AlgebraicGeometry.MeromorphicGerms
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N) (F : LPSOriginalFilledCurve N → ℂ)
    (hF : lpsOriginalFilledChartMeromorphic N hN F)
    (hno : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      ∀ x : MulAction.orbitRel.Quotient
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ,
      0 ≤ meromorphicOrderAt (F ∘ (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N)).symm)
        (chartAt ℂ (Sum.inl x : LPSOriginalFilledCurve N) (Sum.inl x))) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => lpsOriginalNormalizedFilledFunction N hN F (Sum.inl ⟦τ⟧)) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro τ
  let π := lpsOriginalHolomorphicCovectorProjection N
  have hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (lpsOriginalNormalizedFilledFunction N hN F) (π τ) := by
    apply contMDiffAt_iff_source.mpr
    rw [contMDiffWithinAt_iff_contDiffWithinAt]
    have ha := chartNormalizedMeromorphicFunction_analyticAt F hF (π τ)
      (chartAt ℂ (π τ) (π τ)) (mem_chart_target ℂ (π τ)) (hno ⟦τ⟧)
    simpa only [extChartAt_coe_symm,extChartAt_coe,modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm,Set.range_id,Function.comp_def,id_eq,
      lpsOriginalNormalizedFilledFunction] using ha.contDiffAt.contDiffWithinAt
  exact (hg.comp τ (lpsOriginalHolomorphicCovectorProjection_contMDiff N hN τ)).mdifferentiableAt (by decide)
end QEC.Coding.TannerLiftedProduct
