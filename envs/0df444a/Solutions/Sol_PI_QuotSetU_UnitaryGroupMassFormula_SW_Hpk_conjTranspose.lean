-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:16:07.127388+00:00
-- url     : https://prove2.me/submissions/4f59442a-a5ed-40b4-8e08-f04186d31475

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SsetGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_piI_piI
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_epsI_piI
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_star_epsI
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_apply

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
theorem _root_.solution : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [Matrix.conjTranspose_apply, Hpk_apply, Hpk_apply]
  by_cases h : j = piI k r i
  · have h' : i = piI k r j := by rw [h, piI_piI]
    rw [if_pos h', if_pos h, star_epsI, h, epsI_piI]
  · have h' : ¬ i = piI k r j := fun h' => h (by rw [h', piI_piI])
    rw [if_neg h', if_neg h, star_zero]
end PI.QuotSetU.UnitaryGroupMassFormula.SW
