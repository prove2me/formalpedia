-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:57:56.440853+00:00
-- url     : https://prove2.me/submissions/30808646-2e58-49c5-a31e-c4907b8d3794

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic

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
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
open PI PI.QuotSetU
variable {k r : ℕ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution (i : Fin (2 * r + k + 1)) : epsI k r i * epsI k r i = 1 := by
  unfold epsI
  split_ifs <;> norm_num
end PI.QuotSetU.UnitaryGroupMassFormula.SW
