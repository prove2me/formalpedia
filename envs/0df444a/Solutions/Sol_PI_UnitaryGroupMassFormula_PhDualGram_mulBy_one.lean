-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhDualGram.mulBy_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:41:25.966802+00:00
-- url     : https://prove2.me/submissions/a8003495-c230-492a-8862-f49649c688f5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_BeMulByZero
import Theorems.Thm_PI_FglPhSplit_Wk_pt_lg


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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.PhDualGram
open PI.FglGram MvPowerSeries
variable {p : ℕ} [Fact p.Prime] {l ex ph : PowerSeries ℂ_[p]}
namespace PI.UnitaryGroupMassFormula.PhDualGram
theorem _root_.solution (hl0 : PowerSeries.constantCoeff l = 0)
    (hinvl : PowerSeries.subst l ex = PowerSeries.X) {σ : Type} {x : MvPowerSeries σ ℂ_[p]}
    (hx : constantCoeff x = 0) : mulBy l ex 1 x = x := by
  unfold mulBy
  rw [map_one, one_mul]
  exact PI.FglPhSplit.Wk.pt_lg (⟨l, ex, 0⟩ : PI.FglPhSplit.Dat ℂ_[p]) hl0 hinvl hx
end PI.UnitaryGroupMassFormula.PhDualGram
