-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2Character_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:12:48.751205+00:00
-- url     : https://prove2.me/submissions/0c0a593f-ed40-4d2e-90da-51c13a6e7a82

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution : lpsChi4E2Character 0=0 ∧ lpsChi4E2Character 1=1 ∧
    lpsChi4E2Character 2=0 ∧ lpsChi4E2Character 3= -1 := by
  norm_num [lpsChi4E2Character_apply,ZMod.χ₄_apply]
end QEC.Coding.TannerLiftedProduct
