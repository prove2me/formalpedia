-- Prove2me | solution 1 for PI.WGL.LTE.sg_detShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:11:13.164874+00:00
-- url     : https://prove2.me/submissions/c6b9e593-4143-4b63-8f4e-b2e8e0fb5183

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleD
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTE
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC PI.WGL.LTD
namespace PI.WGL.LTE
theorem _root_.solution {n : ℕ} (sg : DomWeight n) (hn : 0 < n) :
    sg.detShift = sg.w ⟨n - 1, by omega⟩ := by
  unfold DomWeight.detShift
  rw [dif_pos hn]
end PI.WGL.LTE
