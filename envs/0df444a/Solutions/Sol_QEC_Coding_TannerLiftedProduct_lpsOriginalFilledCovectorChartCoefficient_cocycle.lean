-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledCovectorChartCoefficient_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:27:27.818753+00:00
-- url     : https://prove2.me/submissions/85f90ef2-6af6-421f-bb45-7e68dd9e9f25

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeLocalDifferentialComparison
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_NormalizedGermUnits
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNativeCovectorCoordinates
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
open Filter Topology QEC.Coding.AlgebraicGeometry.MeromorphicGerms
open scoped Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hN : 4 ∣ N)
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (sigma : LPSOriginalFilledCovectorRepresentatives N hN)
    (x y : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z ∈ ((chartAt ℂ x).symm.trans (chartAt ℂ y)).source) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    let g := (chartAt ℂ x).symm.trans (chartAt ℂ y)
    lpsOriginalFilledCovectorChartCoefficient N hN sigma x z =
      lpsOriginalFilledCovectorChartCoefficient N hN sigma y (g z) * deriv g z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  let e := chartAt ℂ x
  let d := chartAt ℂ y
  let p := e.symm z
  let v : ℂ := mfderiv 𝓘(ℂ) 𝓘(ℂ) e.symm z (1 : ℂ)
  have hp : p ∈ e.source := e.map_target hz.1
  have hpd : p ∈ d.source := hz.2
  have he := lpsOriginalFilledCovectorChart_evaluate N hN sigma x p v hp
  have hd := lpsOriginalFilledCovectorChart_evaluate N hN sigma y p v hpd
  have heDiff : e.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := mdifferentiable_chart x
  have hdDiff : d.MDifferentiable 𝓘(ℂ) 𝓘(ℂ) := mdifferentiable_chart y
  have hinv := heDiff.mdifferentiableAt_symm hz.1
  have hchart := hdDiff.mdifferentiableAt hpd
  have hunit : (mfderiv 𝓘(ℂ) 𝓘(ℂ) e p v : ℂ) = (1 : ℂ) :=
    congrArg (fun L : ℂ →L[ℂ] ℂ => L (1 : ℂ))
      (heDiff.comp_symm_deriv hz.1)
  have heCoeff : sigma p v = lpsOriginalFilledCovectorChartCoefficient N hN sigma x z := by
    have hs := congrArg (fun t : ℂ =>
      lpsOriginalFilledCovectorChartCoefficient N hN sigma x (e p) * t) hunit
    have hh := he.trans (hs.trans (mul_one _))
    simpa only [p, e.right_inv hz.1] using hh
  have hchain := mfderiv_comp_apply z hchart hinv (1 : ℂ)
  rw [mfderiv_eq_fderiv] at hchain
  have hderiv : (mfderiv 𝓘(ℂ) 𝓘(ℂ) d p v : ℂ) = deriv (d ∘ e.symm) z :=
    hchain.symm
  change lpsOriginalFilledCovectorChartCoefficient N hN sigma x z =
    lpsOriginalFilledCovectorChartCoefficient N hN sigma y (d p) * deriv (d ∘ e.symm) z
  rw [← heCoeff, hd]
  exact congrArg (fun t : ℂ =>
    lpsOriginalFilledCovectorChartCoefficient N hN sigma y (d p) * t) hderiv
end QEC.Coding.TannerLiftedProduct
