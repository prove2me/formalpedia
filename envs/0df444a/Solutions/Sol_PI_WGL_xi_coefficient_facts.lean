-- Prove2me | solution 1 for PI.WGL.xi_coefficient_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:51:27.803456+00:00
-- url     : https://prove2.me/submissions/d4f9b288-c1d8-436f-aa01-15de49218c13

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ZScalarVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_EvalInitMinorNormLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_ConstructionXi
import Theorems.Thm_PI_WGL_XiB_xi_last
import Theorems.Thm_PI_WGL_XiB_xi_mem
import Theorems.Thm_PI_WGL_XiB_xi_ne
import Theorems.Thm_PI_WGL_XiB_xi_torus
import Theorems.Thm_PI_WGL_XiB_xi_unitary
import Theorems.Thm_PI_WGL_XiB_xi_unitri


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
theorem _root_.solution : XiFacts := by
  intro n N h lam sg hI
  refine ⟨XiB.xi_ne h lam sg, XiB.xi_mem h lam sg hI, ?_, ?_, ?_, ?_⟩
  · intro g hlow hdiag
    exact XiB.xi_unitri h lam sg g hlow hdiag
  · intro t
    exact XiB.xi_torus h lam sg hI t
  · intro a
    exact XiB.xi_last h lam sg hI a
  · intro x hx
    exact XiB.xi_unitary h lam sg x hx
end PI.WGL
