-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4Phase_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:12:49.913711+00:00
-- url     : https://prove2.me/submissions/22d6c8de-7859-49cf-bd49-89ac84f246d9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChar_four_two


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution : ZMod.stdAddChar (3:ZMod 4)= -ZMod.stdAddChar (1:ZMod 4) := by
  rw [show (3:ZMod 4)=1+2 by decide,AddChar.map_add_eq_mul,lpsChar_four_two]
  ring
end QEC.Coding.TannerLiftedProduct
