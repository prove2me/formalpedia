-- Prove2me | solution 1 for P2M_PI_UnitaryGroupMassFormula_LCG_DetIdxW__c_apply_9834e349ebaa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:18:13.822911+00:00
-- url     : https://prove2.me/submissions/8d068f36-bf74-474e-b956-0fc438e4e2e3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDet

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
theorem _root_.solution (t : Fin k → 𝓞 K) (i : Fin k) : ιc K k t i = algebraMap (𝓞 K) K (t i) := rfl
end PI.UnitaryGroupMassFormula.LCG.DetIdxW
