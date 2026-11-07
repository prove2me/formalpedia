-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilled_projection_contMDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:25:22.271109+00:00
-- url     : https://prove2.me/submissions/e8e4ae44-4ced-42b5-800f-f26b4737d3e5

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspAnalytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_interior_contMDiff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Quotient_projection_contMDiff


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
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun τ : ℍ => (Sum.inl (Quotient.mk (MulAction.orbitRel
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) ℍ) τ) : LPSOriginalFilledCurve N)) := by
  let := lpsOriginalFilledTopology N
  let := lpsGamma0QuotientChartedSpace N hN
  let := lpsOriginalFilledChartedSpace N hN
  exact (lpsOriginalFilled_interior_contMDiff N hN).comp
    (lpsGamma0Quotient_projection_contMDiff N hN)
end QEC.Coding.TannerLiftedProduct
