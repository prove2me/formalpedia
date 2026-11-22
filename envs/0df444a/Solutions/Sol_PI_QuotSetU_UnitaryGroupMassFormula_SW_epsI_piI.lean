-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI_piI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:16:37.910878+00:00
-- url     : https://prove2.me/submissions/313ce0b0-07d2-4aeb-95cd-43ea4d555e2c

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
theorem _root_.solution (i : Fin (2 * r + k + 1)) : epsI k r (piI k r i) = epsI k r i := by
  have hi := i.isLt
  unfold epsI
  rw [piI_val]
  split_ifs <;> first | rfl | omega
end PI.QuotSetU.UnitaryGroupMassFormula.SW
