-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2Gauss_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:16:24.103288+00:00
-- url     : https://prove2.me/submissions/d9f67d43-859d-4572-8adb-2e34cfdf473b

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Gauss_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_four_odd_square


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution : gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))^2= -4 := by
  rw [lpsChi4E2Gauss_eq,mul_pow]
  have h := lpsChar_four_odd_square 1 (by decide)
  norm_num at h ⊢
  rw [h]
  norm_num
end QEC.Coding.TannerLiftedProduct
