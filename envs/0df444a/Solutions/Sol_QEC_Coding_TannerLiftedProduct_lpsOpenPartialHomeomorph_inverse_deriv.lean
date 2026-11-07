-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOpenPartialHomeomorph_inverse_deriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:47:40.292551+00:00
-- url     : https://prove2.me/submissions/28c0f302-3108-40a6-be6d-e20c336d6f37

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCuspQDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialCoefficients
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOpenPartialHomeomorph_inverse_analytic


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (e : OpenPartialHomeomorph ℂ ℂ) (z : ℂ) (hz : z∈e.source)
    (ha : AnalyticAt ℂ e z) (hd : deriv e z≠0) :
    deriv e.symm (e z) * deriv e z = 1 := by
  have hi := lpsOpenPartialHomeomorph_inverse_analytic e z hz ha hd
  have he : (e.symm∘e) =ᶠ[𝓝 z] id := by
    have hn : ∀ᶠ w in 𝓝 z, w∈e.source := e.open_source.mem_nhds hz
    filter_upwards [hn] with w hw
    exact e.left_inv hw
  calc
    deriv e.symm (e z) * deriv e z = deriv (e.symm∘e) z :=
      (deriv_comp z hi.differentiableAt ha.differentiableAt).symm
    _ = deriv id z := he.deriv_eq
    _ = 1 := deriv_id z
end QEC.Coding.TannerLiftedProduct
