-- Prove2me | solution 1 for PI.AddIntG.Wk.lam_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:00:27.631367+00:00
-- url     : https://prove2.me/submissions/35cb4c51-529d-44c4-8c7a-83d9daea9a95

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Theorems.Thm_PI_AddIntG_Wk_lamA_coeff_lam
import Theorems.Thm_PI_AddIntG_Wk_lamA_wser_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.AddIntG PI.AddIntG.Wk
variable {p : ℕ} [Fact p.Prime]
namespace PI.AddIntG.Wk
theorem _root_.solution {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hS : ∀ n, PowerSeries.coeff n wq ∈ S) :
    ∀ e, MvPowerSeries.coeff e (lam wq) ∈ S := by
  intro e
  rw [lamA_coeff_lam]
  exact lamA_wser_mem hS _
end PI.AddIntG.Wk
