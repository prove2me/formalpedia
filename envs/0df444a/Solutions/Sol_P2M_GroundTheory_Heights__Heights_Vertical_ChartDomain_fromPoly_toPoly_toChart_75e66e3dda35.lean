-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_toPoly_toChart_75e66e3dda35
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:21.310247+00:00
-- url     : https://prove2.me/submissions/5152c9de-7a7d-4e48-b5d7-2f91c8572ff2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_toPoly_toChart_090ab285bd50
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_baseToChart_mk_793326c29cbf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_cx_85517b06cadd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_X_2b090bd40426
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_secForm_ecd84404e055
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_chartForm_efb69df01e78

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.ChartDomain
variable {D : Type} [CommRing D] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)
namespace GroundTheory.Heights₂.Heights.Vertical.ChartDomain
theorem _root_.solution :
    ((fromPoly Q j e).comp (toPoly Q j e)).comp (toChart Q j e) = toChart Q j e := by
  apply MvPolynomial.ringHom_ext
  · intro c
    have h : (((fromPoly Q j e).comp (toPoly Q j e)).comp (toChart Q j e)).comp C =
        (toChart Q j e).comp C := by
      apply MvPolynomial.ringHom_ext
      · intro d
        simp only [RingHom.comp_apply, toPoly_toChart, evalF, κ, coe_eval₂Hom, eval₂_C, fromPoly,
          baseToChart_mk, map_C]
      · intro p
        simp only [RingHom.comp_apply, toPoly_toChart, evalF, coe_eval₂Hom, eval₂_C, eval₂_X]
        rcases p with ⟨i, l⟩ | l
        · simp only [parVal, map_sub, fromPoly_X]
          split_ifs
          · rw [map_mul, fromPoly_secForm, mul_zero, sub_zero]
          · rw [map_zero, sub_zero]
        · simp only [parVal, map_sub, fromPoly_X]
          split_ifs
          · rw [map_mul, fromPoly_chartForm, mul_zero, sub_zero]
          · rw [map_zero, sub_zero]
    exact RingHom.congr_fun h c
  · intro l
    simp only [RingHom.comp_apply, toPoly_toChart, evalF, coe_eval₂Hom, eval₂_X, fromPoly_cx]
end GroundTheory.Heights₂.Heights.Vertical.ChartDomain
