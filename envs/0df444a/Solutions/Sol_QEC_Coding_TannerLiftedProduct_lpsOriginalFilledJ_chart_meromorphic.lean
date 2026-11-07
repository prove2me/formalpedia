-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJ_chart_meromorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:36:27.395186+00:00
-- url     : https://prove2.me/submissions/c60808f8-af3a-448c-91f1-6c7b8d25239f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing
import Mathlib.Analysis.Meromorphic.Order
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_cusp_meromorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_interior_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJ_cusp_analytic_nonzero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 4∣N)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z∈(chartAt ℂ x).target) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    MeromorphicAt (fun w : ℂ => lpsOriginalFilledJ N ((chartAt ℂ x).symm w)) z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  cases x with
  | inl y => exact (lpsOriginalFilledJ_interior_analytic N hN y z hz).meromorphicAt
  | inr c =>
    by_cases hz0 : z=0
    · subst z
      exact lpsOriginalFilledJ_cusp_meromorphic N c
    · exact (lpsOriginalFilledJ_cusp_analytic_nonzero N hN c z hz hz0).meromorphicAt
end QEC.Coding.TannerLiftedProduct
