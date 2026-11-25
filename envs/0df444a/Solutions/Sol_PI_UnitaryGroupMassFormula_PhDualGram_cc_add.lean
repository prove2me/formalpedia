-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhDualGram.cc_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:41:21.650951+00:00
-- url     : https://prove2.me/submissions/8044ec58-aedc-4990-96e3-bce345a837ee

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_BeMulByZero
import Theorems.Thm_PI_FglPhSplit_Wk_cc_psubst


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
theorem _root_.solution (hex0 : PowerSeries.constantCoeff ex = 0) (hl0 : PowerSeries.constantCoeff l = 0)
    {σ : Type} {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0) (hy : constantCoeff y = 0) :
    constantCoeff (add l ex x y) = 0 := by
  unfold add pt lg
  exact PI.FglPhSplit.Wk.cc_psubst _ hex0 (by
    rw [map_add, PI.FglPhSplit.Wk.cc_psubst _ hl0 hx, PI.FglPhSplit.Wk.cc_psubst _ hl0 hy, add_zero])
end PI.UnitaryGroupMassFormula.PhDualGram
