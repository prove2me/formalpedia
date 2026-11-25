-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.inv_mul_UH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:18:47.819105+00:00
-- url     : https://prove2.me/submissions/f6fa1072-7687-48e9-8196-d4b2ccb0bfc7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_mul_self

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
    (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  rw [show Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) by
    simp only [Matrix.mul_assoc], hg', Hpk_mul_self]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
