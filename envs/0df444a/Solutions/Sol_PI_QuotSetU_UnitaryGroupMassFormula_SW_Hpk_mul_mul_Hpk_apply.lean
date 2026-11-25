-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_mul_mul_Hpk_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:18:44.68245+00:00
-- url     : https://prove2.me/submissions/ba903ddf-3b37-4400-a772-673b311214be

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_mul_apply
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_Hpk_apply

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
theorem _root_.solution (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (Hpk k r * X * Hpk k r) i j = epsI k r i * X (piI k r i) (piI k r j) * epsI k r j := by
  rw [mul_Hpk_apply, Hpk_mul_apply]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
