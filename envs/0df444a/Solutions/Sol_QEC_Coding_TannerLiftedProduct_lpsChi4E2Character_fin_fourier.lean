-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2Character_fin_fourier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:16:19.170506+00:00
-- url     : https://prove2.me/submissions/8dadb5f9-73bf-429b-af92-c179cd42e7e7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Character_values
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4Phase_three
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Gauss_eq

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (n : ZMod 4) :
    (∑ a : Fin 4,lpsChi4E2Character (a.val:ZMod 4)*ZMod.stdAddChar (n*(a.val:ZMod 4)))=
      lpsChi4E2Character n*gaussSum lpsChi4E2Character (ZMod.stdAddChar (N:=4)) := by
  rw [Fin.sum_univ_four,lpsChi4E2Gauss_eq]
  norm_num [lpsChi4E2Character_apply,ZMod.χ₄_apply]
  have hc := lpsChi4E2Character_values
  fin_cases n
  · change ZMod.stdAddChar (0:ZMod 4)-ZMod.stdAddChar (0:ZMod 4)=lpsChi4E2Character 0*(2*ZMod.stdAddChar (1:ZMod 4))
    rw [hc.1]
    ring
  · change ZMod.stdAddChar (1:ZMod 4)-ZMod.stdAddChar (3:ZMod 4)=lpsChi4E2Character 1*(2*ZMod.stdAddChar (1:ZMod 4))
    rw [hc.2.1,lpsChi4Phase_three]
    ring
  · change ZMod.stdAddChar (2:ZMod 4)-ZMod.stdAddChar (2:ZMod 4)=lpsChi4E2Character 2*(2*ZMod.stdAddChar (1:ZMod 4))
    rw [hc.2.2.1]
    ring
  · change ZMod.stdAddChar (3:ZMod 4)-ZMod.stdAddChar (1:ZMod 4)=lpsChi4E2Character 3*(2*ZMod.stdAddChar (1:ZMod 4))
    rw [hc.2.2.2,lpsChi4Phase_three]
    ring
end QEC.Coding.TannerLiftedProduct
