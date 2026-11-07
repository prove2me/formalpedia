-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2Character_square
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T03:05:05.09926+00:00
-- url     : https://prove2.me/submissions/0539342e-dd22-4ac4-a7fe-eccdfb0a9c8e

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCharacterEisensteinCusps

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (d : ZMod 4) (hd : IsUnit d) :
    lpsChi4E2Character (d^2)=1 := by
  have hq := ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)
  have h : lpsChi4E2Character^2=1 := hq.sq_eq_one
  rw [map_pow,←MulChar.pow_apply' lpsChi4E2Character (by norm_num : (2:ℕ)≠0),h,
    MulChar.one_apply hd]
end QEC.Coding.TannerLiftedProduct
