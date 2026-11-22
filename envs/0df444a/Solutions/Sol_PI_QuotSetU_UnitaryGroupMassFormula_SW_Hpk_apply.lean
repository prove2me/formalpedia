-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:19:51.944801+00:00
-- url     : https://prove2.me/submissions/e55916a2-9e2b-405b-84b4-80ac4bd96d3c

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
theorem _root_.solution (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = piI k r i then epsI k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, epsI, Fin.ext_iff, piI_val]
  split_ifs <;> first | rfl | omega
end PI.QuotSetU.UnitaryGroupMassFormula.SW
