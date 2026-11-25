-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_LCG_DetIdxW__c_inj_c9b0d1123f22
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:47:56.156548+00:00
-- url     : https://prove2.me/submissions/65700b2b-f664-4a60-8f75-d34e2d71cdee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDet
import Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_LCG_DetIdxW__c_apply_9834e349ebaa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.DetIdxW
variable {K : Type} [Field K] [NumberField K] {k : ℕ}
namespace PI.UnitaryGroupMassFormula.LCG.DetIdxW
theorem _root_.solution : Function.Injective (ιc K k) := fun x y h => funext fun c =>
  IsFractionRing.injective (𝓞 K) K (by have := congrFun h c; rwa [ιc_apply, ιc_apply] at this)
end PI.UnitaryGroupMassFormula.LCG.DetIdxW
