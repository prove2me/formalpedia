-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledJDilated_chart_meromorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:18:25.481085+00:00
-- url     : https://prove2.me/submissions/9d0abc5c-f105-4e75-9946-7abe12812241

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJDilated_cusp_meromorphic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJDilated_interior_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledJDilated_cusp_analytic_nonzero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hpos : 0<N) (hN : 4∣N)
    (x : LPSOriginalFilledCurve N) (z : ℂ)
    (hz : letI := lpsOriginalFilledTopology N
      letI := lpsOriginalFilledChartedSpace N hN
      z∈(chartAt ℂ x).target) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    MeromorphicAt (fun w : ℂ => lpsOriginalFilledJDilated N hpos ((chartAt ℂ x).symm w)) z := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  cases x with
  | inl y => exact (lpsOriginalFilledJDilated_interior_analytic N hpos hN y z hz).meromorphicAt
  | inr c =>
    by_cases hz0 : z=0
    · subst z
      exact lpsOriginalFilledJDilated_cusp_meromorphic N hpos c
    · exact (lpsOriginalFilledJDilated_cusp_analytic_nonzero N hpos hN c z hz hz0).meromorphicAt
end QEC.Coding.TannerLiftedProduct
