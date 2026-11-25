-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhDualGram.be_mulBy_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:41:17.510511+00:00
-- url     : https://prove2.me/submissions/c7687478-46a0-47a0-97bb-d68a22dc86ca

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_BeMulByZero
import Theorems.Thm_PI_FglPhSplit_Wk_be_mulBy_zero


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
theorem _root_.solution (hex0 : PowerSeries.constantCoeff ex = 0)
    (hph0 : PowerSeries.constantCoeff ph = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    (hinvl : PowerSeries.subst l ex = PowerSeries.X) {σ : Type} (x : MvPowerSeries σ ℂ_[p])
    {y : MvPowerSeries σ ℂ_[p]} (hy : constantCoeff y = 0) :
    be l ex ph (mulBy l ex 0 x) y = 0 :=
  PI.FglPhSplit.Wk.be_mulBy_zero (⟨l, ex, ph⟩ : PI.FglPhSplit.Dat ℂ_[p]) hex0 hph0 hl0 hinvl x hy
end PI.UnitaryGroupMassFormula.PhDualGram
