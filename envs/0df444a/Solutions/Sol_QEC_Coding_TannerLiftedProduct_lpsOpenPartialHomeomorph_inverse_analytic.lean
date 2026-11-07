-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOpenPartialHomeomorph_inverse_analytic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:23:28.69022+00:00
-- url     : https://prove2.me/submissions/29fecaf8-c9c7-4a51-b8be-8df307cadf4d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspAnalytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular
noncomputable section
open scoped Classical
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (e : OpenPartialHomeomorph ℂ ℂ) (z : ℂ) (hz : z∈e.source)
    (ha : AnalyticAt ℂ e z) (hd : deriv e z≠0) :
    AnalyticAt ℂ e.symm (e z) := by
  apply (analyticAt_comp_iff_of_deriv_ne_zero ha hd).mp
  apply analyticAt_id.congr
  have hn : ∀ᶠ z' in 𝓝 z, z'∈e.source := e.open_source.mem_nhds hz
  filter_upwards [hn] with z' hz'
  exact (e.left_inv hz').symm
end QEC.Coding.TannerLiftedProduct
