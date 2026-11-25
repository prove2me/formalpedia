-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:33:44.976001+00:00
-- url     : https://prove2.me/submissions/601e6b87-df13-4794-8efe-165e3bc808ae

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_piI_piI
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_epsI_piI
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_epsI_mul_self
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_apply
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_mul_apply

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
theorem _root_.solution : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Hpk_mul_apply, Hpk_apply, piI_piI, epsI_piI, Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp [epsI_mul_self]
  · simp [h, Ne.symm h]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
