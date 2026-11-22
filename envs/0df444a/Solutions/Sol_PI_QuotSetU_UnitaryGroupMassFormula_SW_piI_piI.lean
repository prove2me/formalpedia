-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.piI_piI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:51.972695+00:00
-- url     : https://prove2.me/submissions/5bbde0f1-f083-44ab-8b09-5d5a206547d2

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_piI_val

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
theorem _root_.solution (i : Fin (2 * r + k + 1)) : piI k r (piI k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  rw [piI_val, piI_val]
  split_ifs <;> omega
end PI.QuotSetU.UnitaryGroupMassFormula.SW
