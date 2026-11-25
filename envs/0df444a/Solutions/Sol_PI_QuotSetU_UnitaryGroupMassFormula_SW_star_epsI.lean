-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.star_epsI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:12:05.402242+00:00
-- url     : https://prove2.me/submissions/12daa43d-9213-4879-814e-4b821ccd008d

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
theorem _root_.solution (i : Fin (2 * r + k + 1)) : star (epsI k r i) = epsI k r i := by
  unfold epsI
  split_ifs <;> simp
end PI.QuotSetU.UnitaryGroupMassFormula.SW
