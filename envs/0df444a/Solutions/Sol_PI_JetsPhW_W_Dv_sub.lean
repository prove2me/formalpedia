-- Prove2me | solution 1 for PI.JetsPhW.W.Dv_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:47:13.939813+00:00
-- url     : https://prove2.me/submissions/552ee6c9-fa03-4e30-aa58-1e19a2fce207

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_PolarizationDifferenceFormulaHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_HighGOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.W
open PI.JetsPhW
variable {p : ℕ} [Fact p.Prime] {σ : Type*}
namespace PI.JetsPhW.W
theorem _root_.solution (v : PowerSeries ℂ_[p]) (i : σ) (f g : MvPowerSeries σ ℂ_[p]) :
    Dv v i (f - g) = Dv v i f - Dv v i g := by
  simp only [Dv, map_sub, mul_sub]
end PI.JetsPhW.W
