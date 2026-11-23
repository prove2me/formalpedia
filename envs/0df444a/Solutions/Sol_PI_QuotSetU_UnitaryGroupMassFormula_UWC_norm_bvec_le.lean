-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.UWC.norm_bvec_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:46:52.35716+00:00
-- url     : https://prove2.me/submissions/bb5059ed-20ed-4321-9474-05f92dcec91b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MaximalCompactIsCompact
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_bvec_apply


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
theorem _root_.solution (j i : Fin (2 * r + k + 1)) : ‖bvec j i‖ ≤ 1 := by
  rw [bvec_apply]; split_ifs <;> simp
end PI.QuotSetU.UnitaryGroupMassFormula.UWC
