-- Prove2me | solution 1 for PI.WfLogWork.formal_logarithm_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:46:55.491909+00:00
-- url     : https://prove2.me/submissions/278adb93-2190-4125-b322-fce14e5837d0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_CoefWfIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_FormalLogarithmHolds
import Theorems.Thm_PI_WfLogWork_omega_coeff_mem
import Theorems.Thm_PI_ExpIntWProof_inv_nat_mem_Wf
import Theorems.Thm_PI_WfLogWork_Wp_le_Wf
import Theorems.Thm_PI_WfLogWork_coefWf_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WfLogWork
open PI.ExpIntWProof PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.WfLogWork
theorem _root_.solution : PI.WfLogL := by
  intro p _ W wq h1 h2 h3 h4 h6 hW
  rw [coefWf_iff]
  intro n
  rw [AddIntG.flog, PowerSeries.coeff_mk]
  split_ifs with hn
  · exact zero_mem _
  · rw [div_eq_mul_inv]
    exact mul_mem (Wp_le_Wf (omega_coeff_mem h1 h2 h3 h4 h6 hW (n - 1))) (inv_nat_mem_Wf p n hn)
end PI.WfLogWork
