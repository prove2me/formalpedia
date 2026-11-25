-- Prove2me | solution 1 for PI.WfLogWork.C_memS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:16.071392+00:00
-- url     : https://prove2.me/submissions/57f711ee-0377-4ab0-996e-f476ce8da7ec

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_CoefWfIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_DXEqDerivative
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_SubstMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittLogarithm_FormalLogarithmHolds
import Theorems.Thm_PI_WfLogWork_mem_SerS_iff

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
theorem _root_.solution {S : Subring ℂ_[p]} {a : ℂ_[p]} (ha : a ∈ S) :
    ((algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a : PowerSeries ℂ_[p]) : MvPowerSeries Unit ℂ_[p]) ∈ SerS S Unit := by
  rw [mem_SerS_iff]
  intro n
  rw [Algebra.algebraMap_eq_smul_one, map_smul, PowerSeries.coeff_one, smul_eq_mul]
  split_ifs <;> simp [ha]
end PI.WfLogWork
