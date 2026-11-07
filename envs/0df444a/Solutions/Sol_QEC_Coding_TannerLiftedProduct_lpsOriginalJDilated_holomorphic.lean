-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalJDilated_holomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:15:32.449705+00:00
-- url     : https://prove2.me/submissions/1dd4712b-f646-4315-8623-1c714cb9f874

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularFunction
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSEisensteinDifference
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDilatedModularFunction
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsE2AffineMatrix_det
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJInvariant_holomorphic


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) (hN : 0<N) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalJDilated N hN) := by
  have hp : 0<(lpsE2AffineMatrix N hN 0).det.val := by
    rw [lpsE2AffineMatrix_det];exact_mod_cast hN
  exact lpsOriginalJInvariant_holomorphic.comp (UpperHalfPlane.mdifferentiable_smul hp)
end QEC.Coding.TannerLiftedProduct
