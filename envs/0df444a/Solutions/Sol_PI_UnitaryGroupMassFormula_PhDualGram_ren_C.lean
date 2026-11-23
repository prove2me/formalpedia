-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.PhDualGram.ren_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:04.967807+00:00
-- url     : https://prove2.me/submissions/506b204d-f586-4bb3-aafc-345423805e1c

import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DualGramSubstitution_HasSubstRen
import Theorems.Thm_PI_UnitaryGroupMassFormula_PhDualGram_ren_apply

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
variable {p : ℕ} [Fact p.Prime]
variable {σ τ : Type} [Finite σ] (r : σ → τ)
namespace PI.UnitaryGroupMassFormula.PhDualGram
theorem _root_.solution (c : ℂ_[p]) : ren r (C c : MvPowerSeries σ ℂ_[p]) = C c := by
  rw [ren_apply, MvPowerSeries.subst_C]
end PI.UnitaryGroupMassFormula.PhDualGram
