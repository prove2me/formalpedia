-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.UWC.norm_H_bvec_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:02.363703+00:00
-- url     : https://prove2.me/submissions/aa1b92dc-23ab-4f60-a253-20441284a649

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_UWC_norm_epsI
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_UWC_norm_bvec_le
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_Hpk_mulVec_apply


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
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.UWC
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula.SW
variable {k r : ℕ}
namespace PI.QuotSetU.UnitaryGroupMassFormula.UWC
theorem _root_.solution (j i : Fin (2 * r + k + 1)) : ‖(Hpk k r *ᵥ bvec j) i‖ ≤ 1 := by
  rw [Hpk_mulVec_apply, norm_mul, norm_epsI, one_mul]
  exact norm_bvec_le _ _
end PI.QuotSetU.UnitaryGroupMassFormula.UWC
