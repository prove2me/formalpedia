-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedToFullMeromorphic_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:29:53.012613+00:00
-- url     : https://prove2.me/submissions/cc6ceee1-2a8a-4e2b-893e-66f7744994d1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicGerms
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalMeromorphicRestriction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    Function.Injective (lpsOriginalGeneratedToFullMeromorphic N hpos hN) := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  exact (lpsOriginalGeneratedToFullMeromorphic N hpos hN).injective
end QEC.Coding.TannerLiftedProduct
