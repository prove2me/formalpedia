-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferentialLinearEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:06:53.550917+00:00
-- url     : https://prove2.me/submissions/b37ee484-f884-4279-a3e4-9b62060e166f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledDifferentialLinearEquiv_apply

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN) :
    (lpsOriginalFilledDifferentialLinearEquiv N hN).symm sectionForm =
      lpsOriginalHolomorphicCovectorCuspForm N hN sectionForm := by
  apply (lpsOriginalFilledDifferentialLinearEquiv N hN).injective
  rw [LinearEquiv.apply_symm_apply, lpsOriginalFilledDifferentialLinearEquiv_apply,
    lpsOriginalHolomorphicCovectorCuspForm_filled]
end QEC.Coding.TannerLiftedProduct
