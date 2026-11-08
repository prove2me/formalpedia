-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferentialLinearEquiv_inverse_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:28:32.868659+00:00
-- url     : https://prove2.me/submissions/5fdb6444-0098-4607-8422-b75cc2213918

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledDifferential
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledConnected
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicDifferentialComparison
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledDifferentialLinearEquiv_symm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hN : 4 ∣ N)
    (sectionForm : LPSOriginalHolomorphicCovectorSections N hN) (τ : ℍ) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    (lpsOriginalFilledDifferentialLinearEquiv N hN).symm sectionForm τ =
      sectionForm (lpsOriginalHolomorphicCovectorProjection N τ)
        (mfderiv 𝓘(ℂ) 𝓘(ℂ) (lpsOriginalHolomorphicCovectorProjection N) τ (1 : ℂ)) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  rw [lpsOriginalFilledDifferentialLinearEquiv_symm_apply,
    lpsOriginalHolomorphicCovectorCuspForm_apply]
  rfl
end QEC.Coding.TannerLiftedProduct
