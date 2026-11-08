-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalFilledForgetLevel_isProperMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:06:38.396941+00:00
-- url     : https://prove2.me/submissions/481448e0-5dfe-4f7a-90c9-f8a0a3724168

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledForgetLevel_continuous
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_compactSpace
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalFilledTopology_t2Space


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N M : ℕ) [NeZero N] [NeZero M] (hNM : N ∣ M) :
    letI := lpsOriginalFilledTopology N
    letI := lpsOriginalFilledTopology M
    IsProperMap (lpsOriginalFilledForgetLevel N M hNM) := by
  let := lpsOriginalFilledTopology N
  let := lpsOriginalFilledTopology M
  let := lpsOriginalFilledTopology_compactSpace M
  let := lpsOriginalFilledTopology_t2Space N
  exact (lpsOriginalFilledForgetLevel_continuous N M hNM).isProperMap
end QEC.Coding.TannerLiftedProduct
