-- Prove2me | solution 1 for PI.WGL.LTD.card_lt_sz
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:26.41695+00:00
-- url     : https://prove2.me/submissions/5f4aa22b-59b5-4735-a015-8ca9b07f2ec8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTD
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTA PI.WGL.LTM PI.WGL.LTC
namespace PI.WGL.LTD
theorem _root_.solution {n K : ℕ} (sg : DomWeight n) (sz : Fin K → ℕ) (hshape : shapeDeg sz = sg.natW)
    (t : Fin n) : (Finset.univ.filter fun k => t.1 < sz k).card = sg.natW t := by
  rw [← hshape]; rfl
end PI.WGL.LTD
