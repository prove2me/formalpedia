-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4UnitPhase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:40:11.422209+00:00
-- url     : https://prove2.me/submissions/afd6158b-013f-417b-b491-5d75d5d25951

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularDilation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspLocalFactors
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Character_values
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Gauss_eq
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4Phase_three


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex
open scoped MatrixGroups UpperHalfPlane ModularForm
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (d : ZMod 4) (hd : IsUnit d) :
    2*ZMod.stdAddChar d=gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))*lpsChi4E2Character d := by
  have hzero : ¬IsUnit (0:ZMod 4) := by decide
  have htwo : ¬IsUnit (2:ZMod 4) := by decide
  fin_cases d
  · change IsUnit (0:ZMod 4) at hd
    exact False.elim (hzero hd)
  · change 2*ZMod.stdAddChar (1:ZMod 4)=gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))*lpsChi4E2Character 1
    rw [lpsChi4E2Character_values.2.1,lpsChi4E2Gauss_eq,mul_one]
  · change IsUnit (2:ZMod 4) at hd
    exact False.elim (htwo hd)
  · change 2*ZMod.stdAddChar (3:ZMod 4)=gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4))*lpsChi4E2Character 3
    rw [lpsChi4E2Character_values.2.2.2,lpsChi4E2Gauss_eq,lpsChi4Phase_three]
    ring
end QEC.Coding.TannerLiftedProduct
