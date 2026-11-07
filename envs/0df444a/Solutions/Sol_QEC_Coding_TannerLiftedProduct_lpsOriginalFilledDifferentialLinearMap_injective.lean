-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledDifferentialLinearMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:47:14.597805+00:00
-- url     : https://prove2.me/submissions/a93de6be-8397-48b1-8764-e62a4aa4bedb

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialGluing
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledDifferential
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledDifferential_injective
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilled_isManifold


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Pointwise Modular Bundle
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hN : 4∣N) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledChartedSpace N hN
    letI := lpsOriginalFilled_isManifold N hN
    Function.Injective (lpsOriginalFilledDifferentialLinearMap N hN) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledChartedSpace N hN
  let := lpsOriginalFilled_isManifold N hN
  intro f g he
  apply lpsOriginalFilledDifferential_injective N hN
  exact congrArg (fun s => s.toFun) he
end QEC.Coding.TannerLiftedProduct
