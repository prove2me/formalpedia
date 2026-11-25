-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.zCost_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:54:20.867126+00:00
-- url     : https://prove2.me/submissions/da0ce72a-dd66-4383-a25f-8fed28eba145

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZCostOf
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_zeta_cost_of_smooth_deriv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
namespace PI.UnitaryGroupMassFormula.UsCost
theorem _root_.solution (hS : ZSmooth) (hD : ZDeriv) (hDS : DirSize) : ZCost :=
  zeta_cost_of_smooth_deriv hS hD hDS
end PI.UnitaryGroupMassFormula.UsCost
