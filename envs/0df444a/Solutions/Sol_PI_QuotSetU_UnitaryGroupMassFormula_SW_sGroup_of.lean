-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.sGroup_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:34:15.92844+00:00
-- url     : https://prove2.me/submissions/412cef62-4d06-4b1e-a162-affb8fb5cfe3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnipotentRadicalContracting
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_IsClosedS
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_isClosed_S
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_one_mem_S
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_mem_S
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_mem_S

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
variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.SW
theorem _root_.solution (hUW : UWCompact) : SsetGroup := by
  intro k r z hz hT
  exact ⟨isClosed_S (hUW k r z hz hT), one_mem_S, fun a ha b hb => mul_mem_S ha hb,
    fun a ha => inv_mem_S ha⟩
end PI.QuotSetU.UnitaryGroupMassFormula.SW
