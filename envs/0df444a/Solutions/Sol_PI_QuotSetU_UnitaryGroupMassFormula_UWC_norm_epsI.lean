-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.UWC.norm_epsI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:22.798251+00:00
-- url     : https://prove2.me/submissions/db036c91-0522-4723-96fe-1e59e8d20cea

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.UWC
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW
variable {k r : ℕ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.UWC
theorem _root_.solution (i : Fin (2 * r + k + 1)) : ‖epsI k r i‖ = 1 := by
  unfold epsI; split_ifs <;> simp
end PI.QuotSetU.UnitaryGroupMassFormula.UWC
