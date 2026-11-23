-- Prove2me | solution 1 for PI.AddIntG.Wk.lamA_wser_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:56.026809+00:00
-- url     : https://prove2.me/submissions/dc9351de-d3f7-452b-b75f-97a28405a61f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffPowMemS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdditiveIntegralGroups_CoeffWSeriesVarZero
import Theorems.Thm_PI_AddIntG_Wk_lamA_coeff_wser

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
theorem _root_.solution {S : Subring ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hS : ∀ n, PowerSeries.coeff n wq ∈ S)
    (n : ℕ) : PowerSeries.coeff n (wser wq) ∈ S := by
  rw [lamA_coeff_wser]; split_ifs
  · exact hS _
  · exact S.zero_mem
end PI.AddIntG.Wk
