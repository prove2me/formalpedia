-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_quarter_cusp_not_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:26:01.748478+00:00
-- url     : https://prove2.me/submissions/e45d4b8e-0069-45a6-b9b1-fdf30825e9f0

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Gauss_ne_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Twist_quarter_cusp_tendsto

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    ¬UpperHalfPlane.IsZeroAtImInfty (lpsChi4E2Twist ∣[(2:ℤ)] lpsE2PrimeCuspMatrix 4) := by
  intro hz
  have he := tendsto_nhds_unique lpsChi4E2Twist_quarter_cusp_tendsto hz
  exact (div_ne_zero (by norm_num : (-12:ℂ)≠0) lpsChi4E2Gauss_ne_zero) he
end QEC.Coding.TannerLiftedProduct
