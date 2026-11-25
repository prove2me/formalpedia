-- Prove2me | solution 1 for PI.QuotSetU.UnitaryGroupMassFormula.SW.nilpotent_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:17:47.960318+00:00
-- url     : https://prove2.me/submissions/cd67a795-fa90-4416-834f-7ee01646de90

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mem_Nset_iff
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_nc_one
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_nc_mul
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_nc_inv
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_inv_mem_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_mul_mem_UH
import Theorems.Thm_PI_QuotSetU_UnitaryGroupMassFormula_SW_one_mem_UH


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
theorem _root_.solution : NGroup := by
  intro k r
  refine ⟨(mem_Nset_iff 1).2 ⟨one_mem_UH, nc_one⟩, fun a ha b hb => ?_, fun a ha => ?_⟩
  · obtain ⟨haU, haN⟩ := (mem_Nset_iff a).1 ha
    obtain ⟨hbU, hbN⟩ := (mem_Nset_iff b).1 hb
    exact (mem_Nset_iff _).2 ⟨mul_mem_UH haU hbU, nc_mul haN hbN⟩
  · obtain ⟨haU, haN⟩ := (mem_Nset_iff a).1 ha
    exact (mem_Nset_iff _).2 ⟨inv_mem_UH haU, nc_inv haU haN⟩
end PI.QuotSetU.UnitaryGroupMassFormula.SW
