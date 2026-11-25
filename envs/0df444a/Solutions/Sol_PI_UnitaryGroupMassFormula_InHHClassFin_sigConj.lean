-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.InHHClassFin.sigConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:40:36.244799+00:00
-- url     : https://prove2.me/submissions/2fa93bb1-bea0-4597-99fa-8d6ccabe3779

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianClassFiniteness_SigConj
import Theorems.Thm_Formalism_UG_Final_SigConj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.InHHClassFin
namespace PI.UnitaryGroupMassFormula.InHHClassFin
theorem _root_.solution : SigConj := by
  intro I τ
  ext a
  show τ (star a) = starRingEnd ℂ (τ a)
  exact I.cm.cmUnram.2.1 τ a
end PI.UnitaryGroupMassFormula.InHHClassFin
