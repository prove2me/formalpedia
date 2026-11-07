-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2Gauss_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:19:08.021129+00:00
-- url     : https://prove2.me/submissions/75a63a14-abe2-4581-9a50-53cf78af6720

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Gauss_sq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution : gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))≠0 := by
  intro h
  have hs := lpsChi4E2Gauss_sq
  rw [h] at hs
  norm_num at hs
end QEC.Coding.TannerLiftedProduct
