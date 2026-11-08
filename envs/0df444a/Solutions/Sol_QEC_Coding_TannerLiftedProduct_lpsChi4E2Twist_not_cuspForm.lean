-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsChi4E2Twist_not_cuspForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:59:27.983493+00:00
-- url     : https://prove2.me/submissions/27765759-99db-4367-a545-86278df6fec1

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuadraticEisensteinCuspGeneral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSChi4Eisenstein
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsChi4E2Twist_quarter_cusp_not_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped UpperHalfPlane ModularForm MatrixGroups Manifold
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    ¬∃ f : CuspForm (CongruenceSubgroup.Gamma0 16 : Subgroup (GL (Fin 2) ℝ)) 2,
      (f:ℍ→ℂ)=lpsChi4E2Twist := by
  rintro ⟨f,hf⟩
  have hz := CuspFormClass.zero_at_infty_slash f (g:=lpsE2PrimeCuspMatrix 4)
  rw [hf] at hz
  exact lpsChi4E2Twist_quarter_cusp_not_zero hz
end QEC.Coding.TannerLiftedProduct
