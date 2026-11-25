-- Prove2me | solution 1 for PI.WGL.BrInt.map_ratSmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:08:58.588253+00:00
-- url     : https://prove2.me/submissions/bf4493ae-ea83-4dab-b486-917b17353f3d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_HwIrred
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalB
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionBrInt
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions MvPolynomial
open PI.WGL.BrInt
open Formalism.REAL Formalism.GradedWeylDivisibility
variable {σ : Type}
namespace PI.WGL.BrInt
theorem _root_.solution (q : ℚ) (p : MvPolynomial σ ℚ) :
    map (algebraMap ℚ ℂ) (q • p) = ((q : ℚ) : ℂ) • map (algebraMap ℚ ℂ) p := by
  ext m
  simp [MvPolynomial.coeff_map, MvPolynomial.coeff_smul]
end PI.WGL.BrInt
