-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJReciprocal_chart_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:18:18.976197+00:00
-- url     : https://prove2.me/submissions/2eaeef53-58ae-4a81-857f-49f9dd115042

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJReciprocal_cusp_analytic_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJReciprocal_interior_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJReciprocal_cusp_analytic_nonzero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 4∣N)
    (a : ℂ) (ho : ∀ τ : ℍ, lpsOriginalJInvariant τ≠a)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z∈(chartAt ℂ x).target) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    AnalyticAt ℂ (fun w : ℂ => lpsOriginalFilledJReciprocal N a ((chartAt ℂ x).symm w)) z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  cases x with
  | inl y => exact lpsOriginalFilledJReciprocal_interior_analytic N hN a ho y z hz
  | inr c =>
    by_cases hz0 : z=0
    · subst z
      exact lpsOriginalFilledJReciprocal_cusp_analytic_zero N a c
    · exact lpsOriginalFilledJReciprocal_cusp_analytic_nonzero N hN a ho c z hz hz0
end QEC.Coding.TannerLiftedProduct
