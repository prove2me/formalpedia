-- Prove2me | solution 1 for PI.WGL.numbers_dominant_large
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:12:09.295145+00:00
-- url     : https://prove2.me/submissions/afd123cd-2db7-4fe8-84cc-e4967889cf2b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinTopCoefficient_NumMore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionNum
import Theorems.Thm_PI_GTNum_abs_cBr_le_cBd
import Theorems.Thm_PI_GTNum_cBr_ne_zero
import Theorems.Thm_PI_GTNum_degZ_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL
open Formalism.BasicNotions MvPolynomial
namespace PI.WGL
theorem _root_.solution : Numbers := by
  intro n N h lam sg hI
  exact ⟨PI.GTNum.cBr_ne_zero h lam sg hI, PI.GTNum.abs_cBr_le_cBd h lam sg hI,
    PI.GTNum.degZ_eq h lam sg⟩
end PI.WGL
