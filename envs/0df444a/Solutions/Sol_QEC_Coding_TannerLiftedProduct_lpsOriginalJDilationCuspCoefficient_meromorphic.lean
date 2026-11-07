-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJDilationCuspCoefficient_meromorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:10:07.762351+00:00
-- url     : https://prove2.me/submissions/605b480c-ce1d-4e61-919b-e2130812f35a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilationCuspE4_analytic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJDilationCuspDelta_analytic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N]
    (hN : 0<N) (ρ : SL(2,ℤ)) :
    MeromorphicAt (lpsOriginalJDilationCuspCoefficient N hN ρ) 0 := by
  exact (analyticAt_const.mul ((lpsOriginalJDilationCuspE4_analytic N hN ρ).pow 3)).meromorphicAt.div
    (lpsOriginalJDilationCuspDelta_analytic N hN ρ).meromorphicAt
end QEC.Coding.TannerLiftedProduct
