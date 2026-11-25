-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.mul_inv_UH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:07:22.179819+00:00
-- url     : https://prove2.me/submissions/517e4ef0-f5fa-46e9-a3ac-955103312d2c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_mul_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_eq_UH

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
theorem _root_.solution {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    g * g⁻¹ = 1 := by
  rw [inv_eq_UH hg]
  exact mul_eq_one_comm.mp (inv_mul_UH hg)
end PI.QuotSetU.UnitaryGroupMassFormula.SW
