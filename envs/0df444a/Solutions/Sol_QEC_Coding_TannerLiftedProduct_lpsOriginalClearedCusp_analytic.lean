-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalClearedCusp_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:01:41.535186+00:00
-- url     : https://prove2.me/submissions/b65f0a0f-57fa-4b48-87f9-b7c406d1a484

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedMonomial_analytic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : N≠0) (B : ℕ)
    (P : Polynomial (Polynomial ℂ)) : AnalyticAt ℂ (lpsOriginalClearedCusp N B P) 0 := by
  classical
  exact P.support.analyticAt_sum fun k _=> (P.coeff k).support.analyticAt_sum fun i _=>
    analyticAt_const.mul (lpsOriginalClearedMonomial_analytic N hN B i k)
end QEC.Coding.TannerLiftedProduct
