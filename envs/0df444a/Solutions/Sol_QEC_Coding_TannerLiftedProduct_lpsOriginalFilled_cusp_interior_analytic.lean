-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_cusp_interior_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:25:20.690646+00:00
-- url     : https://prove2.me/submissions/af7cf0e9-4254-4cee-8ed5-b0211bd0fad0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspAnalytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOpenPartialHomeomorph_inverse_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_interior_cusp_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
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
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 4∣N)
    (x : MulAction.orbitRel.Quotient
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ)
    (c : CuspOrbits (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)))
    (z : ℂ) (hz : letI := lpsOriginalFilledTopology N
      z∈((lpsOriginalFilledCuspChart N c).symm.trans
        (lpsOriginalFilledInteriorChart N hN x)).source) :
    letI := lpsOriginalFilledTopology N
    AnalyticAt ℂ ((lpsOriginalFilledCuspChart N c).symm.trans
      (lpsOriginalFilledInteriorChart N hN x)) z := by
  let := lpsOriginalFilledTopology N
  let e := (lpsOriginalFilledCuspChart N c).symm.trans
    (lpsOriginalFilledInteriorChart N hN x)
  have hf := lpsOriginalFilled_interior_cusp_analytic N hN x c (e z)
    (e.map_source hz)
  have hi := lpsOpenPartialHomeomorph_inverse_analytic e.symm (e z)
    (e.map_source hz) hf.1 hf.2
  simpa only [OpenPartialHomeomorph.symm_symm,e.left_inv hz] using hi
end QEC.Coding.TannerLiftedProduct
